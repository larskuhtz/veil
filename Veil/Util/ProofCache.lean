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
* **The kernel is the only checker; the cache only skips search.**
  Every hit is re-elaborated
  against the *live* environment (`Meta.check` + `isDefEq` with the goal)
  before the goal is assigned — the same level of checking a fresh
  reconstruction gets at sweep time — and every persistence point
  (`addDecl` in `#gen_theorems`/`#prove_action`/`#prove_vc`)
  still kernel-checks. Any failure — corrupt file, changed definitions,
  missing constants, toolchain drift — degrades to a miss and a fresh
  solve; staleness cannot produce a wrong ✅.
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

private unsafe def loadEntryUnsafe (path : FilePath) :
    IO (Entry × CompactedRegion) :=
  unpickle Entry path

@[implemented_by loadEntryUnsafe]
private opaque loadEntryImpl (path : FilePath) : IO (Entry × CompactedRegion)

/-- Look up a closed statement. Returns the cached sorry-free proof term if
an entry exists, deserializes, and states *exactly* `stmt` (structural
equality) under the current schema — anything else (including a corrupt or
other-toolchain file, via the `catch`) is `none`. The caller still must
re-check the proof against the live environment before using it. -/
def find? (opts : Options) (stmt : Expr) : IO (Option Entry) := do
  let path := entryPath opts stmt
  unless ← path.pathExists do return none
  let loaded? ← try some <$> loadEntryImpl path catch _ => pure none
  let some (entry, region) := loaded? | return none
  regions.modify (·.push region)
  unless entry.schemaVersion == schemaVersion do return none
  unless entry.statement == stmt do return none
  return some entry

/-- Store a successful discharge. Atomic (temp + rename): last writer wins,
concurrent dischargers and parallel lake jobs are safe. Never throws — a
full disk or read-only cache dir degrades to "no cache", logged on
`trace.veil.cache` by the caller via the `Bool` result. -/
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
    return true
  catch _ =>
    return false

/-- Record a hit (after the caller's re-check succeeded). -/
def recordHit : IO Unit :=
  stats.modify fun (h, s) => (h + 1, s)

end Veil.ProofCache
