import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Core.Tools.Verifier.Manager
import Veil.Core.Tools.Verifier.Results
import Std.Sync.Mutex
import Veil.Util.Multiprocessing
import Veil.Util.Meta

namespace Veil.Verifier

open Lean Elab Command Std

-- FIXME: this should be in `EnvExtensions.lean`, but putting it there triggers
-- the bug fixed in [#10217](https://github.com/leanprover/lean4/pull/10217).
-- Placing it here as a workaround until the fix ships in a stable Lean.
/-- Holds the state of the VCManager for the current file. -/
initialize vcManager : Std.Mutex (VCManager VCMetadata SmtResult) ← Std.Mutex.new (← VCManager.new vcManagerCh)

/-- Errors thrown inside the manager loop. The loop runs detached from any
command snapshot (registering its infinite task would hang the build), so
exceptions it catches are invisible to the editor; they are recorded here and
surfaced as warnings by `awaitFilteredWithLogging` on its next poll. -/
initialize managerLoopErrors : IO.Ref (Array String) ← IO.mkRef #[]

/-- Solver-relevant option values as they were when the named module's VCs
(and their dischargers) were generated, i.e. at `#gen_spec`. Dischargers
capture their elaboration context — including options — at creation time, so
a `set_option veil.smt.* ... in #check_invariants` does *not* affect solving;
check commands compare against this record to warn about such silent
mismatches (`warnIfSolverOptionsChangedSinceVCGen`). -/
initialize solverOptionsAtVCGen : IO.Ref (Option (Name × Array (String × String))) ← IO.mkRef none

def sendNotification (notification : ManagerNotification VCMetadata SmtResult) : CommandElabM Unit := do
  let _ ← vcManagerCh.send notification

/-- Run a computation with exclusive access to the VCManager.
    Use this for batching multiple VC operations atomically. -/
def withVCManager (f : IO.Ref (VCManager VCMetadata SmtResult) → CommandElabM α) : CommandElabM α :=
  vcManager.atomically f

def reset (managerId : ManagerId) : CommandElabM Unit := sendNotification (.reset managerId)
def startAll : CommandElabM Unit := sendNotification .startAll
def startFiltered (filter : VCMetadata → Bool) : CommandElabM Unit := sendNotification (.startFiltered filter)

def isDoesNotThrow (m : VCMetadata) : Bool := m.propertyName? == some `doesNotThrow

/-- Start ready dischargers from the enabled set until the number in flight
reaches the core count: spawn each task (`Discharger.run` only *spawns* — the
elaboration/solving runs on the thread pool), send it to the task
registration channel for the frontend to register via `logSnapshotTask`, and
write the started discharger back into its node.

Must be called with the `vcManager` lock held, as part of a handler's single
critical section: holding the lock, the `(vc, discharger)` pairs returned by
`readyTasks` are *current*, so the write-back cannot clobber concurrent
frontend updates (interactive `@[veil]` registrations, added dischargers, a
reset). `BaseIO`, so the handler cannot fail or be interrupted between
spawning tasks and the caller's single `ref.set` — spawned work and recorded
state stay consistent. -/
private def fillAvailableSlotsLocked (mgr : VCManager VCMetadata SmtResult)
    : BaseIO (VCManager VCMetadata SmtResult) := do
  let mut mgr := mgr
  let numCores ← getNumCores
  let inFlight ← mgr.inFlightCount
  let ready := (← mgr.readyTasks).take (numCores - inFlight)
  for (vc, discharger) in ready do
    let discharger' ← discharger.run
    if let some task := discharger'.task then
      -- Send to channel for frontend to register (instead of registering directly here)
      let _ ← Veil.taskRegistrationCh.send { task, cancelTk := discharger'.cancelTk }
    let vc' := { vc with dischargers := vc.dischargers.set! discharger.id.dischargerId discharger' }
    mgr := { mgr with nodes := mgr.nodes.insert vc.uid vc' }
  return mgr

/-- Cancel every discharger of `mgr` and drain queued-but-not-yet-registered
task registrations, cancelling each. Called by both reset paths so replacing
the manager state never leaks running work: tasks already registered with the
language server are cancelled by it on re-elaboration, but entries still queued
in `taskRegistrationCh` would otherwise never be registered *nor* cancelled,
and running dischargers would keep computing for a manager generation whose
results are ignored (see `Discharger.cancelTk` for the cancellation latency
contract). Public so reset behavior can be regression-tested deterministically
(`VeilTest/Regression/VerifierServerRaces.lean`). -/
def cancelAbandonedWork (mgr : VCManager VCMetadata SmtResult) : IO Unit := do
  mgr.cancelAllDischargers
  while true do
    match ← Veil.taskRegistrationCh.tryRecv with
    | some info => info.cancelTk.set
    | none => break

/-- Starts a separate task (on a dedicated thread) that runs the VCManager.
If this is called multiple times, each call will reset the VC manager. -/
def runManager (cancelTk? : Option IO.CancelToken := none) : CommandElabM Unit := do
  let cancelTk := cancelTk?.getD (← IO.CancelToken.new)
  let managerLoop ← Command.wrapAsyncAsSnapshot (fun () => do
    -- dbg_trace "({← IO.monoMsNow}) [Manager] Starting manager loop"
    while true do
      try
        -- blocks until we get a notification
        -- NOTE: this `get` is really problematic, as it increases the threadpool size
        let notification := (← vcManagerCh.recv).get
        -- Each notification is processed in ONE `vcManager.atomically` section:
        -- decisions (`readyTasks`) and write-backs see the same state, frontend
        -- writers (`withVCManager`, `@[veil]` registration, the frontend-side
        -- reset in `runManager`) are serialized against the whole handler, and
        -- the single `ref.set` at the end makes a failed handler roll back
        -- wholesale instead of leaving torn state. Holding the lock here is
        -- cheap: `Discharger.run` only spawns a task, channel sends are
        -- non-blocking, and discharger task bodies never take this mutex.
        match notification with
        | .dischargerResult dischargerId res => do
          vcManager.atomically (fun ref => do
            let mut mgr ← ref.get
            if dischargerId.managerId != mgr._managerId then
              return
            mgr ← mgr.recordDischargerResult dischargerId res
            -- Release the just-completed discharger's task handle: it has fired
            -- and its result is now in `_dischargerResults`, but `Discharger.task`
            -- still references the completed `Task`, which retains its
            -- `SnapshotTree` (message log + trace state). On large protocols
            -- (1500+ VCs) these accumulate to multiple GB. The handle has no
            -- consumers once the result is recorded, so null it to let Lean
            -- RC-free the snapshot tree. Must happen BEFORE the refill below:
            -- `fillAvailableSlotsLocked` reads `inFlightCount` off this manager.
            if let some vc := mgr.nodes[dischargerId.vcId]? then
              if let some d := vc.dischargers[dischargerId.dischargerId]? then
                let d' := { d with task := none }
                let vc' := { vc with dischargers := vc.dischargers.set! dischargerId.dischargerId d' }
                mgr := { mgr with nodes := mgr.nodes.insert dischargerId.vcId vc' }
            -- Refill AFTER recordDischargerResult so freshly woken
            -- alternatives and unlocked dependents can all be scheduled.
            mgr ← fillAvailableSlotsLocked mgr
            ref.set mgr)
          Frontend.notify
        | .startAll => do
          vcManager.atomically (fun ref => do
            ref.set (← fillAvailableSlotsLocked (← ref.get).enableAll))
          Frontend.notify
        | .startFiltered filter => do
          vcManager.atomically (fun ref => do
            ref.set (← fillAvailableSlotsLocked ((← ref.get).enableMatching filter)))
          -- Wake pollers (they re-check `isDoneFiltered` under their own lock)
          Frontend.notify
        | .fill => do
          vcManager.atomically (fun ref => do
            ref.set (← fillAvailableSlotsLocked (← ref.get)))
          Frontend.notify
        | .reset managerId => vcManager.atomically (fun ref => do
          let mut mgr ← ref.get
          if mgr._managerId != managerId then
            return
          -- Reap abandoned work before dropping the only references to it
          cancelAbandonedWork mgr
          mgr ← VCManager.new vcManagerCh (currentManagerId := mgr._managerId)
          ref.set mgr)
      catch ex =>
        -- Log errors but continue processing to prevent the manager loop from
        -- dying. The single-`ref.set` discipline above means a failed handler
        -- left the manager unchanged. Nothing logged here reaches the editor
        -- (the loop is not registered with `logSnapshotTask`), so also record
        -- the error for `awaitFilteredWithLogging` to surface as a warning.
        let msg ← ex.toMessageData.toString
        dbg_trace "[VCManager] Error in manager loop: {msg}"
        managerLoopErrors.modify (·.push msg)
  ) cancelTk
  vcServerStarted.atomically (fun ref => do
    if !(← ref.get) then
      -- Start the manager task but DON'T register with logSnapshotTask.
      -- The manager loop is infinite, so registering it would hang the build.
      -- Discharger tasks are registered by runFilteredAsync/waitFilteredSync instead.
      -- dbg_trace "({← IO.monoMsNow}) [Manager] Starting manager loop"
      let _ ← (managerLoop ()).asTask
    else
      vcManager.atomically (fun managerRef => do
        let mgr ← managerRef.get
        -- Reap abandoned work before dropping the only references to it
        cancelAbandonedWork mgr
        let mgr ← VCManager.new vcManagerCh (currentManagerId := mgr._managerId)
        managerRef.set mgr)
    ref.set true
  )

/-- Demote error-severity diagnostics in a discharger's snapshot tree to
information severity, recursively through child snapshots (lean-smt's async
solver machinery registers tasks as children of the discharger's snapshot and
logs its failures there — e.g. "unable to prove goal … Reason: TIMEOUT" —
which is why demoting the discharger callback's own message log was never
enough).

Rationale: a discharger is one *attempt* at a VC. Its outcome is routed
through the manager as a `DischargerResult` and aggregated into the VC's
effective status ("conclusive outcomes win over sibling errors"), which the
check command's results display reports — with error severity — exactly when
the VC *effectively* failed. The raw attempt diagnostics are therefore
redundant, and worse: an error-severity message from a failed attempt whose
VC was covered by a sibling (seed retry, WP/TR alternative form) reddens an
otherwise-green build, positioned confusingly at `#gen_spec` (where the
discharger's snapshot context was captured). Demoting — not dropping — keeps
the text available for debugging without failing green builds. -/
private partial def sanitizeDischargerSnapshotTree (t : Language.SnapshotTree) :
    BaseIO Language.SnapshotTree := do
  let demote (msg : Message) : Message :=
    if msg.severity == .error then { msg with severity := .information } else msg
  let msgLog := t.element.diagnostics.msgLog
  let msgLog := { msgLog with
    reported := msgLog.reported.map demote
    unreported := msgLog.unreported.map demote }
  let diagnostics ← Language.Snapshot.Diagnostics.ofMessageLog msgLog
  let children ← t.children.mapM fun child => do
    return { child with task := (← BaseIO.mapTask sanitizeDischargerSnapshotTree child.task) }
  return { t with element := { t.element with diagnostics }, children }

/-- Log any pending discharger tasks from the channel via `logSnapshotTask`
(non-blocking). The tree is routed through `sanitizeDischargerSnapshotTree`
asynchronously (never blocking registration on discharger completion); the
cancellation token still reaches the *original* task. Note this is the single
registration site for discharger tasks — the model-check compilation tasks
and the results-display callback (`runFilteredAsync`) are registered
elsewhere and deliberately keep their error severities. -/
private partial def logPendingDischargerTasks : CommandElabM Unit := do
  if let some info ← Veil.taskRegistrationCh.tryRecv then
    let sanitized ← BaseIO.mapTask sanitizeDischargerSnapshotTree info.task
    Command.logSnapshotTask { stx? := none, cancelTk? := info.cancelTk, task := sanitized }
    logPendingDischargerTasks

private def ensureExistingTheoremMatches (fullName : Name) (statement : Expr) : TermElabM Unit := do
  let some info := (← getEnv).find? fullName
    | return
  unless ← Meta.isDefEq info.type statement do
    throwError "cannot generate VC theorem `{fullName}` because a declaration with that name already exists with a different type"

/-- Cross-witness structural-sharing state for theorem persistence. The
per-VC proof witnesses are ~95 % identical clump-normalisation chains, but
each was elaborated in its own discharger task, so consecutive witnesses are
almost entirely *structurally* equal while sharing almost nothing
*physically*. Sharing each witness against this accumulated state before
`addDecl` collapses that duplication in memory — the environment holds every
persisted proof until olean serialization, which at reconstruction scale
(~3 800 × ~85 K-object witnesses ≈ 15 GB unshared) is otherwise the peak-
memory driver of `#gen_theorems` — and in olean size. Only ever touched from
the command-elaboration thread (`addProvenVCTheorem`). Reset when a
persistence-enabled await begins, so state never leaks across manager
generations. -/
initialize witnessShareState : IO.Ref (ShareCommon.State Lean.ShareCommon.objectFactory) ←
  IO.mkRef default

private def addProvenVCTheorem (vc : VerificationCondition VCMetadata SmtResult)
    (witness? : Option Witness)
    (regen? : Option (CommandElabM Witness)) : CommandElabM Unit := do
  -- IDEMPOTENCE FAST PATH: if the theorem constant already exists — persisted
  -- incrementally by `persistProvenIncrementally` while the sweep was running,
  -- or `#gen_theorems` invoked twice — verify the statement matches and return
  -- WITHOUT resolving the witness: resolution may run the regen closure, a
  -- full re-elaboration (SMT query included) per VC.
  let fullName := (← getCurrNamespace).append vc.name
  if (← getEnv).contains fullName then
    liftTermElabM do ensureExistingTheoremMatches fullName (← vc.toVCStatement.type)
    return
  -- TRUSTED-STUB FAST PATH (`veil.gen.trustedTheoremStubs`, default true).
  -- When the discharge was trusted-SMT-based, the stored witness slot carries
  -- `sorryAx` — under lazy regen it is exactly the 1-node sentinel, and
  -- without lazy regen it is the full `Eq.mpr` normalisation chain whose
  -- *leaf* is the axiom. Either way the real proof's trust base is the
  -- trusted axiom, so persisting `sorryAx <statement>` directly is
  -- trust-equivalent — and skips both failure modes of witness
  -- materialisation at scale: the serial re-elaboration of the regen
  -- closure (a second SMT run per VC) and the O(action × clump) chain in
  -- memory/olean. Reconstruction runs (`veil.smt.trust = false`) never take
  -- this path: their witnesses contain no `sorryAx`.
  let statementOnly := veil.gen.statementOnlyTheorems.get (← getOptions)
  let useTrustedStub :=
    statementOnly ||
    (veil.gen.trustedTheoremStubs.get (← getOptions) && witness?.any (·.hasSorry))
  -- Resolve the witness. A *sorry-free* stored witness is a real proof (eager
  -- retention, streaming persistence, or an interactive `@[veil]` theorem) —
  -- use it directly, never re-elaborate. A stored witness containing `sorryAx`
  -- is either the 1-node lazy-regen sentinel (regen closure present:
  -- materialise the real witness) or a full eager trust-mode chain (no regen
  -- closure: the chain itself is the proof).
  let witness? : Option Witness ←
    if useTrustedStub then
      pure none  -- constructed below, from the statement
    else some <$> match witness?, regen? with
      | some w, some regen => if w.hasSorry then regen else pure w
      | some w, none => pure w
      | none, some regen => regen
      | none, none => throwError "no witness and no regeneration closure for VC `{vc.name}`"
  -- Under `veil.gen.statementOnlyTheorems` every stub is a deliberate,
  -- option-gated choice: a per-declaration "declaration uses `sorry`"
  -- warning ×N (thousands of lines on a ~3800-VC module) is pure noise, and the batch
  -- pass logs one summary instead. `veil.gen.trustedTheoremStubs` behavior
  -- is deliberately unchanged.
  let suppressSorryWarning : TermElabM Unit → TermElabM Unit :=
    if statementOnly then (withOptions (warn.sorry.set · false) ·) else id
  liftTermElabM <| suppressSorryWarning do
    let statement ← vc.toVCStatement.type
    let witness ← match witness? with
      | some w => do
        let w ← instantiateMVars w
        -- Collapse cross-witness structural duplication before the proof
        -- enters the environment (see `witnessShareState`).
        witnessShareState.modifyGet fun s => s.shareCommon w
      | none => Meta.mkSorry statement (synthetic := false)
    let _ ← addVeilTheorem vc.name statement witness
    return ()

/-- Rolling state of the incremental persist pass, carried across the poll
ticks of one `awaitFilteredWithLogging` run. -/
private structure IncrementalPersistState where
  /-- Manager generation `settled` belongs to; a reset restarts VC ids, so a
  generation change invalidates the whole state. -/
  managerId : ManagerId := 0
  /-- VCs already persisted or terminally skipped this generation. -/
  settled : Std.HashSet VCId := {}
  /-- `VCManager.recordedResultCount` at the last pass — the short-circuit:
  when no new discharger result arrived, there is nothing new to persist and
  the pass returns without walking the DAG. -/
  seenResults : Nat := 0

/-- One incremental-persistence pass (used by `#gen_theorems`'s await loop):
walk the VCs in dependency order and, for every finished VC with a *retained*
witness, add its theorem to the environment now — while other dischargers are
still running — then release the witness immediately
(`VCManager.releasePersistedWitness`). This is what makes `#gen_theorems`
scale in reconstruction mode (`veil.gen.streamTheorems`): peak memory holds
only the completed-but-not-yet-persisted frontier instead of every witness.
(The discharger side must cooperate: `resultPromise` is resolved with a
witness-stripped result — a resolved promise would otherwise pin every
witness for the discharger's lifetime, silently defeating this release.)

VCs whose witness would need regeneration (lazy-dropped) are deliberately left
to the final batch pass: regenerating re-runs elaboration and the SMT query,
and doing that concurrently with a live sweep steals solver cores from
in-flight dischargers (near-boundary VCs would time out spuriously).

A VC is persisted only after every upstream VC (within `filter`) is settled:
unlike the batch pass — which runs after every VC is done — this pass observes
in-flight states, and a witness may reference an upstream VC's theorem
constant.

Concurrency: classification runs on an immutable manager *snapshot*, entirely
outside the lock — the manager mutex is on the dischargers' result-recording
hot path, and holding it across a DAG walk (or worse, `addProvenVCTheorem`)
would stall the whole sweep. The lock is taken only to snapshot (`ref.get`)
and per release write (re-checking the generation). Staleness is benign: a VC
that completes after the snapshot is picked up by a later pass, and `force`
runs one final unconditional pass when the await completes. Must run on the
command-elaboration thread (environment mutation). -/
private def persistProvenIncrementally (filter : VCMetadata → Bool)
    (state : IncrementalPersistState) (force : Bool := false) :
    CommandElabM IncrementalPersistState := do
  let mgr ← vcManager.atomically fun ref => ref.get
  let managerId := mgr._managerId
  let state := if managerId == state.managerId then state
    else { managerId, settled := {}, seenResults := 0 }
  let recorded := mgr.recordedResultCount
  if !force && recorded == state.seenResults then
    return state
  let stubsOn := veil.gen.trustedTheoremStubs.get (← getOptions)
  let order := mgr.vcIdsInDependencyOrder filter
  let orderSet := order.foldl (init := (∅ : Std.HashSet VCId)) (·.insert ·)
  let mut settled := state.settled
  for vcId in order do
    if settled.contains vcId then continue
    let upstream := (mgr.upstream[vcId]?.getD {}).toArray.filter orderSet.contains
    if upstream.any (fun u => !settled.contains u) then continue
    match mgr.vcFinalStatus? vcId with
    | none => continue  -- still running: picked up by a later pass
    | some .proven =>
      match mgr.provenWitnessOrRegen? vcId with
      | some (vc, (some w, regen?)) =>
        -- A retained `sorryAx` witness persists as a statement-only stub
        -- (free) only when stubs are on; otherwise persisting it would
        -- regenerate — leave that to the batch pass.
        if !w.hasSorry || stubsOn then
          addProvenVCTheorem vc (some w) regen?
          vcManager.atomically fun ref => do
            let cur ← ref.get
            if cur._managerId == managerId then
              ref.set (cur.releasePersistedWitness vcId)
          settled := settled.insert vcId
      | some (_, (none, _)) => pure ()  -- lazy-dropped: batch pass
      | none => settled := settled.insert vcId  -- proven without witness (trace VCs)
    | some _ => settled := settled.insert vcId  -- terminally failed: batch skips it too
  return { state with settled, seenResults := recorded }

/-- Poll for discharger tasks from the manager and register them with `logSnapshotTask`.
    Waits until all VCs matching the filter are done, then returns the results.
    This enables profiler trace propagation by registering tasks on the calling thread.

    With `persistIncrementally` (used by `#gen_theorems`), each poll iteration
    also persists finished VCs with retained witnesses and releases their
    witnesses (`persistProvenIncrementally`) — this must only be requested
    from the command-elaboration thread (`waitFilteredSync`), never from the
    async path, where environment mutations would be silently lost. -/
private def awaitFilteredWithLogging (filter : VCMetadata → Bool)
    (persistIncrementally : Bool := false)
    : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  let mut persistState : IncrementalPersistState := {}
  if persistIncrementally then
    witnessShareState.set default
  while true do
    logPendingDischargerTasks
    -- Surface manager-loop errors where the user is looking; the loop itself
    -- cannot log to the editor (it is not registered with `logSnapshotTask`).
    for err in ← managerLoopErrors.modifyGet fun errs => (errs, #[]) do
      logWarning m!"VC manager loop error: {err}"
    if persistIncrementally then
      persistState ← persistProvenIncrementally filter persistState
    -- Snapshot under the lock, render outside it (`toResults` pretty-prints).
    let mgr ← vcManager.atomically fun ref => ref.get
    if mgr.isDoneFiltered filter then
      let results ← liftCoreM (mgr.toResults filter)
      if persistIncrementally then
        -- One final unconditional pass: persist and release VCs that
        -- completed between the last short-circuited tick and `isDone`, so
        -- the batch pass afterwards is a pure idempotence check.
        let _ ← persistProvenIncrementally filter persistState (force := true)
      return results
    IO.sleep 10
  panic! "unreachable"

/-- Start VCs matching the filter and run the callback asynchronously when done.
Uses `wrapAsyncAsSnapshot` so that errors from the callback are reported to the user.
This task also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Note: Widget display does not work in the callback since it runs in an async context. -/
def runFilteredAsync (filter : VCMetadata → Bool)
    (callback : VerificationResults VCMetadata SmtResult → CommandElabM Unit) : CommandElabM Unit := do
  startFiltered filter
  let cancelTk ← IO.CancelToken.new
  let wrappedTask ← Command.wrapAsyncAsSnapshot (fun () => do
    let results ← awaitFilteredWithLogging filter
    callback results) cancelTk
  let task ← (wrappedTask ()).asTask (prio := .dedicated)
  Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task := task }

/-- Start VCs matching the filter and wait synchronously for completion.
Returns the results on the main thread, allowing widget display.
This also polls for discharger tasks from the manager and registers them with
`logSnapshotTask`, enabling profiler trace propagation.
Warning: This blocks the elaborator until all matching VCs complete.

With `persistIncrementally` (`#gen_theorems`), finished VCs with retained
witnesses are persisted to the environment while the remaining dischargers are
still running, and their witnesses released immediately — see
`persistProvenIncrementally`. -/
def waitFilteredSync (filter : VCMetadata → Bool)
    (persistIncrementally : Bool := false) : CommandElabM (VerificationResults VCMetadata SmtResult) := do
  startFiltered filter
  awaitFilteredWithLogging filter persistIncrementally

/-! ## Witness-size instrumentation (`veil.report.witnessSizes`) -/

/-- One measured proof witness: the discharger that produced it, its heap
object count (DAG-aware, `Lean.Expr.numObjs`), and whether it is
trusted-SMT-based (contains `sorryAx`). -/
structure WitnessSizeEntry where
  discharger : Name
  numObjs : Nat
  trusted : Bool
deriving Inhabited

/-- Global registry of measured witness sizes, filled by dischargers when
`veil.report.witnessSizes` is enabled and read by the verification-results
report. Cumulative per Lean module elaboration; the report deduplicates by
discharger name (later entries win). -/
initialize witnessSizeRegistry : IO.Ref (Array WitnessSizeEntry) ← IO.mkRef #[]

/-- Measure `witness` and record it in `witnessSizeRegistry`. Called by
dischargers right after witness elaboration — the only point where the full
witness exists regardless of `veil.lazyWitnessRegen`. -/
def recordWitnessSize (discharger : Name) (witness : Expr) : IO Unit := do
  let n ← witness.numObjs
  witnessSizeRegistry.modify
    (·.push { discharger := discharger, numObjs := n, trusted := witness.hasSorry })

/-- Add theorem declarations for all already-proven VCs matching `filter`.

This must run on the command elaboration thread, not in the manager task: it
mutates the current Lean environment by adding theorem constants whose proofs
are the witnesses returned by successful dischargers. Declarations are added in
the manager DAG's dependency order so downstream proof terms can refer to
upstream VC theorem constants. -/
def addProvenTheoremsInDependencyOrder (filter : VCMetadata → Bool) : CommandElabM Unit := do
  let mgr ← vcManager.atomically fun ref => ref.get
  -- UX: materialising a lazily-dropped witness re-runs its discharger — a
  -- full elaboration plus SMT query per VC, serially on this thread. That
  -- degradation is otherwise silent (`#gen_theorems` just takes a sweep's
  -- worth of solver time, single-threaded), so when it is about to happen at
  -- scale, say so and name the remedy. The threshold only separates "a few
  -- stragglers" (fine) from "the whole module" (the misconfiguration).
  let ns ← getCurrNamespace
  let env ← getEnv
  -- With statement-only persistence the stub path short-circuits before
  -- witness resolution — no regeneration will run, so no warning.
  let statementOnly := veil.gen.statementOnlyTheorems.get (← getOptions)
  let regenCount : Nat := if statementOnly then 0 else
    mgr.vcIdsInDependencyOrder filter |>.foldl (init := 0) fun n vcId =>
      match mgr.provenWitnessOrRegen? vcId with
      | some (vc, (none, some _)) => if env.contains (ns.append vc.name) then n else n + 1
      | _ => n
  if regenCount ≥ 50 then
    logWarning m!"`#gen_theorems` is about to materialise {regenCount} proof \
      witnesses by re-elaborating their dischargers serially (one full proof \
      search per VC — the witnesses were dropped during the sweep, see \
      `veil.lazyWitnessRegen`). For large modules verified with proof \
      reconstruction (`veil.smt.trust false`), set \
      `veil.gen.streamTheorems true` before `#gen_spec` instead: dischargers \
      then retain their witnesses and `#gen_theorems` persists each one \
      incrementally while the sweep is still running."
  let mut persisted : Nat := 0
  for vcId in mgr.vcIdsInDependencyOrder filter do
    if let some (vc, (witness?, regen?)) := mgr.provenWitnessOrRegen? vcId then
      addProvenVCTheorem vc witness? regen?
      persisted := persisted + 1
  -- One summary instead of a per-declaration "uses `sorry`" warning ×N
  -- (suppressed in `addProvenVCTheorem` for this deliberate, option-gated
  -- mode).
  if statementOnly && persisted > 0 then
    let checked := if veil.smt.trust.get (← getOptions) then "checked by the solver"
      else "reconstructed and kernel-checked (`veil.smt.trust false`)"
    logInfo m!"persisted {persisted} VC theorems as statement-only `sorryAx` \
      stubs (`veil.gen.statementOnlyTheorems`): their proofs were {checked} \
      during the sweep, then discarded."

/-- Solve-free statement-stub pass — the `veil.gen.statementOnlyTheorems`
path of `#gen_theorems`: persist every generated
induction VC matching `filter` as a statement-only `sorryAx` stub *without
starting or awaiting any discharger*. The statements exist from `#gen_spec`'s
SMT-free VC generation, and a stub carries no verification claim — so nothing
needs solving to emit one. Consequences of solve-freedom:

* **Both encodings of a cell are stubbed** (the WP and TR forms are distinct
  statements under distinct names, `<action>_<prop>` / `<action>_<prop>_tr`) —
  there is no "which form proved" fact to select by, and neither stub claims
  anything.
* VCs that already reached a terminal non-proven status (a check command ran
  earlier in this file and the VC failed: ❌/💥/⏱/❓) are deliberately NOT
  stubbed — a theorem-shaped constant for a known-failed VC invites accidental
  reliance — and are counted in the summary instead.
* Trace VCs are skipped, as in the proven-theorem batch pass.

The summary reports how many stubs had in fact been proven by the time of
emission, but that count is incidental (e.g. the sweep a preceding
`#check_invariants` ran) — the stubs themselves never certify a sweep. Must
run under `veil.gen.statementOnlyTheorems` (it drives the stub path of
`addProvenVCTheorem`). -/
def addStatementStubs (filter : VCMetadata → Bool) : CommandElabM Unit := do
  unless veil.gen.statementOnlyTheorems.get (← getOptions) do
    throwError "addStatementStubs requires `veil.gen.statementOnlyTheorems`"
  let mgr ← vcManager.atomically fun ref => ref.get
  let vcs := mgr.nodes.values.toArray.qsort (·.uid < ·.uid)
  let mut stubbed := 0
  let mut proven := 0
  let mut skippedFailed := 0
  for vc in vcs do
    unless vc.metadata matches .induction _ do continue
    unless filter vc.metadata do continue
    match mgr.vcFinalStatus? vc.uid with
    | some .proven =>
      addProvenVCTheorem vc none none
      stubbed := stubbed + 1
      proven := proven + 1
    | some _ => skippedFailed := skippedFailed + 1
    | none =>
      addProvenVCTheorem vc none none
      stubbed := stubbed + 1
  let mut msg := m!"persisted {stubbed} VC statements as statement-only \
    `sorryAx` stubs (`veil.gen.statementOnlyTheorems`) — solve-free: a stub \
    carries no verification claim"
  if proven > 0 then
    msg := msg ++ m!" ({proven} of them happened to be proven by this file's \
      sweep at emission time; the stubs do not record that)"
  if skippedFailed > 0 then
    msg := msg ++ m!"; {skippedFailed} VCs with a non-proven terminal status \
      were not stubbed"
  logInfo msg

end Veil.Verifier
