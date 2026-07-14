import Lean
import Batteries.Util.Pickle
import Veil.Base

/-! # Content-addressed proof cache (`veil.cache.proofs`)

The incrementality layer below lake's file granularity: a
content-addressed on-disk cache of *proof terms*, consulted by the Veil
discharge tactics before they search (SMT + lean-smt reconstruction) and
written after every successful sorry-free discharge.

Design (the load-bearing invariants):

* **The key is the statement.** An entry is addressed by the closed goal
  statement's structural `Expr.hash` and carries the full statement `Expr`;
  a lookup compares the stored statement against the live goal, so a hash
  collision is a *miss*, never a wrong answer. Because a proof term's
  validity is independent of which solver/seed/timeout found it, no solver
  configuration enters the key — which is exactly what lets a retry-ladder
  cell hit an entry stored by any of its attempts.
* **The check is never skipped on a hit; the cache only skips search.**
  Every hit is re-checked before anything depends on it, in one of two
  modes (`veil.cache.kernelReplay`): the default re-elaborates against the
  *live* environment (`Meta.check` + `isDefEq` with the goal) — the same
  level of checking a fresh reconstruction gets at sweep time; kernel
  replay makes the *kernel* the only checker — persistence commands
  `addDecl` the cached term directly (`replayPersist?`) and check-only
  discharges kernel-check it against a discarded scratch environment.
  Every persistence point (`addDecl` in
  `#gen_theorems`/`#prove_action`/`#prove_vc`) kernel-checks in
  either mode. Any failure — corrupt file, changed definitions, missing
  constants, toolchain drift — degrades to a miss and a fresh solve;
  staleness cannot produce a wrong ✅.
* **Successes only**: timeouts must stay
  retryable and counterexamples re-findable, so only sorry-free proof
  terms are stored. Reconstruction mode only — trusted-mode witnesses
  carry `sorryAx` and certify nothing by themselves.
* Entries are written atomically (temp file + rename), so concurrent
  dischargers and parallel lake jobs can share one cache directory.

Serialization is `Batteries.Util.Pickle` (olean-grade `saveModuleData` /
`readModuleData`): DAG-aware — witness `Expr`s are ~95 % shared
normalisation chains — and mmap-loaded. Loaded regions are retained for
the process lifetime (like imported oleans): the proof `Expr`s escape
into the environment. `readModuleData` validates the toolchain githash,
so toolchain bumps invalidate wholesale via the load `catch`. -/

open Lean System

namespace Veil.ProofCache

/-- Bump when the entry layout or the semantics of cached proofs change.
A version mismatch is a miss. -/
def schemaVersion : Nat := 1

/-- One cached discharge: the exact statement this entry certifies (the
collision guard and the semantic key), the sorry-free proof term, and the
wall-clock cost of the solve that produced it (informational). -/
structure Entry where
  schemaVersion : Nat
  statement : Expr
  proof : Expr
  solveMs : Nat
deriving Inhabited

/-- `CompactedRegion`s backing unpickled entries. Freed never: the proof
`Expr`s escape into goals/the environment, exactly like olean-imported
constants — dropping a region while a reference lives is UB. -/
initialize regions : IO.Ref (Array CompactedRegion) ← IO.mkRef #[]

/-- (hits, stores) this process. Read by the sweep-results summary line and
by tests; per-hit detail is on `trace.veil.cache`. -/
initialize stats : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

def statsHits : IO Nat := return (← stats.get).1
def statsStores : IO Nat := return (← stats.get).2

def cacheDir (opts : Options) : FilePath :=
  ⟨veil.cache.dir.get opts⟩

/-- Entry path for a statement: one file per statement hash. The hash is
only an address — `find?` compares the stored statement itself. -/
def entryPath (opts : Options) (stmt : Expr) : FilePath :=
  cacheDir opts / s!"{stmt.hash}.vpc"

/-- Per-phase wall time of one `find?`:
what a hit costs *before* any checking. Collected
unconditionally (two clock reads); reported by callers on
`trace.veil.cache`. -/
structure LookupTiming where
  /-- `pathExists` + unpickle (mmap load, region registration), µs. -/
  unpickleUs : Nat := 0
  /-- Guards on the loaded entry: schema check, statement structural `BEq`
  (stored vs live), sorry-guard on the proof, µs. -/
  beqUs : Nat := 0

private unsafe def loadEntryUnsafe (path : FilePath) :
    IO (Entry × CompactedRegion) :=
  unpickle Entry path

@[implemented_by loadEntryUnsafe]
private opaque loadEntryImpl (path : FilePath) : IO (Entry × CompactedRegion)

/-- Look up a closed statement. Returns the cached sorry-free proof term if
an entry exists, deserializes, states *exactly* `stmt` (structural
equality) under the current schema, and contains no `sorryAx` (a stored
entry never does — see `store` — so a sorry inside is a foreign/corrupt
file, and accepting it would let a poisoned cache smuggle `sorryAx` past a
kernel re-check, which proves any `sorryAx`-backed term happily). Anything
else (including a corrupt or other-toolchain file, via the `catch`) is
`none`. The caller still must re-check the proof against the live
environment before using it. -/
def find? (opts : Options) (stmt : Expr) : IO (Option Entry × LookupTiming) := do
  let path := entryPath opts stmt
  let t0 ← IO.monoNanosNow
  unless ← path.pathExists do
    return (none, { unpickleUs := ((← IO.monoNanosNow) - t0) / 1000 })
  let loaded? ← try some <$> loadEntryImpl path catch _ => pure none
  let t1 ← IO.monoNanosNow
  let some (entry, region) := loaded?
    | return (none, { unpickleUs := (t1 - t0) / 1000 })
  regions.modify (·.push region)
  let ok := entry.schemaVersion == schemaVersion
    && entry.statement == stmt
    && !entry.proof.hasSorry
  let t2 ← IO.monoNanosNow
  let timing : LookupTiming :=
    { unpickleUs := (t1 - t0) / 1000, beqUs := (t2 - t1) / 1000 }
  return (if ok then some entry else none, timing)

/-- Whether this process has already run the store-time GC. -/
initialize gcRan : IO.Ref Bool ← IO.mkRef false

/-- Age-based GC (`veil.cache.maxAgeDays`): once per
process, at the first successful store, delete entries whose mtime is older
than the cutoff (and day-old `.tmp` strays from crashed writers). "Now" is
`refPath`'s own mtime — the entry this process just stored — avoiding any
wall-vs-monotonic clock mismatch. Hits do not refresh mtime (nothing
touches files on the hit path), so a hit-only entry re-solves once per
cutoff period and re-enters fresh. Never throws; runs only when a store
already happened, so a fully-warm build never pays the scan. -/
def gcIfDue (opts : Options) (refPath : FilePath) : IO Unit := do
  let days := veil.cache.maxAgeDays.get opts
  if days == 0 then return
  if ← gcRan.modifyGet fun b => (b, true) then return
  try
    let now := (← refPath.metadata).modified.sec
    let mut deleted := 0
    for e in ← (cacheDir opts).readDir do
      let m ← try e.path.metadata catch _ => continue
      let age := now - m.modified.sec
      let stale :=
        (e.path.extension == some "vpc" && age > (days * 86400 : Int)) ||
        (e.path.extension == some "tmp" && age > 86400)
      if stale then
        try IO.FS.removeFile e.path catch _ => pure ()
        deleted := deleted + 1
    if deleted > 0 then
      let entriesWord := if deleted == 1 then "entry" else "entries"
      let daysWord := if days == 1 then "day" else "days"
      IO.eprintln s!"veil.cache: GC deleted {deleted} {entriesWord} older than {days} {daysWord}"
  catch _ => pure ()

/-- Store a successful discharge. Atomic (temp + rename): last writer wins,
concurrent dischargers and parallel lake jobs are safe. Never throws — a
full disk or read-only cache dir degrades to "no cache", logged on
`trace.veil.cache` by the caller via the `Bool` result. The first store of
a process also triggers the age-based GC (`gcIfDue`). -/
def store (opts : Options) (stmt proof : Expr) (solveMs : Nat) : IO Bool := do
  try
    let dir := cacheDir opts
    IO.FS.createDirAll dir
    let path := entryPath opts stmt
    let tmp := dir / s!"{stmt.hash}.{← IO.monoNanosNow}.tmp"
    pickle tmp { schemaVersion, statement := stmt, proof, solveMs : Entry }
      `veilProofCache
    IO.FS.rename tmp path
    stats.modify fun (h, s) => (h, s + 1)
    gcIfDue opts path
    return true
  catch _ =>
    return false

/-- Record a hit (after the caller's re-check succeeded). -/
def recordHit : IO Unit :=
  stats.modify fun (h, s) => (h + 1, s)

/-- Kernel replay (gated on `veil.cache.kernelReplay`):
command-level kernel replay for the persistence paths (`#prove_vc`,
`#prove_action` cells). On a cache hit for `stmt`, hands the
cached term straight to `addDecl` under `name` — that `addDecl` IS the
kernel check of the cached proof (the §2 ground rule: every hit is
kernel-checked before anything depends on it; this path makes the kernel
the *only* checker, skipping the tactic entry and the elaborator-level
`Meta.check`+`isDefEq` a discharger hit pays on top).

Returns the `addDecl` wall time (ms) when the theorem was added this way;
`none` on a disabled cache, a miss, or a kernel rejection — the caller
falls back to its fresh-solve path, so a stale or corrupt entry can never
fail a build, and the fresh proof's `store` then overwrites the bad entry.

Two `Lean.addDecl` internals this function must handle (v4.28):

* under `Elab.async` (lake's default) a `thmDecl`'s kernel check runs in a
  *background task* — a poisoned entry would fail the build later instead
  of raising here. The replay add runs with `Elab.async` disabled so a
  `KernelException` is thrown synchronously and caught;
* a *failed* `addDecl` registers the declaration as an axiom (Lean's
  follow-up-error suppression) and leaves the name occupied, which would
  make the fallback solve's own `addDecl` fail with `alreadyDeclared` —
  so the whole environment is restored on failure. -/
def replayPersist? (name : Name) (levelParams : List Name) (stmt : Expr) :
    CoreM (Option Nat) := do
  let opts ← getOptions
  if !veil.cache.proofs.get opts || !veil.cache.kernelReplay.get opts
      || veil.smt.trust.get opts then
    return none
  if stmt.hasExprMVar || stmt.hasFVar || stmt.hasLevelMVar then
    return none
  let (some entry, timing) ← find? opts stmt | return none
  let envBefore ← getEnv
  let t0 ← IO.monoMsNow
  try
    withOptions (Elab.async.set · false) do
      addDecl (.thmDecl { name, levelParams, type := stmt, value := entry.proof })
  catch ex =>
    setEnv envBefore
    if ex.isInterrupt then throw ex
    trace[veil.cache] "cached proof for {name} failed the kernel check — re-solving"
    return none
  let t1 ← IO.monoMsNow
  recordHit
  trace[veil.cache] "♻ kernel replay {name}; phases[µs]: \
    unpickle={timing.unpickleUs} beq={timing.beqUs} \
    kernelAddDecl={(t1 - t0) * 1000} (stored solve: {entry.solveMs} ms)"
  return some (t1 - t0)

end Veil.ProofCache
