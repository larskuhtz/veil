module

public meta import Veil.Frontend.DSL.Module.Elaborators.Core
public meta import Veil.Frontend.DSL.Tactic
public meta import Veil.Core.UI.Verifier.AssertionErrors
public meta import Veil.Frontend.DSL.Module.VCGen
public meta import Veil.Core.Tools.Verifier.Server
public meta import Veil.Core.Tools.Verifier.Results
public meta import Veil.Core.UI.Verifier.VerificationResults

public meta section

open Lean Parser Elab Command Term
open scoped Veil.Extract
namespace Veil
/-- Solver-relevant options as (name, value) pairs. Used to detect when a
check command runs under different solver options than the VCs' dischargers
captured at `#gen_spec` (see `Verifier.solverOptionsAtVCGen`). -/
private def solverRelevantOptionValues (opts : Options) : Array (String × String) := #[
  ("veil.solver", toString (veil.solver.get opts)),
  ("veil.smt.timeout", toString (veil.smt.timeout.get opts)),
  ("veil.smt.finiteModelFind", toString (veil.smt.finiteModelFind.get opts)),
  ("veil.smt.trust", toString (veil.smt.trust.get opts)),
  ("veil.smt.seed", toString (veil.smt.seed.get opts)),
  ("veil.smt.retries", toString (veil.smt.retries.get opts)),
  ("veil.smt.retryTimeout", toString (veil.smt.retryTimeout.get opts)),
  -- Not a solver option, but discharger-captured all the same: witness
  -- retention for streaming `#gen_theorems` persistence.
  ("veil.gen.streamTheorems", toString (veil.gen.streamTheorems.get opts))]

/-- Warn when solver options in scope at a check command differ from those
captured when the VCs were generated. Dischargers elaborate their proof terms
in the `#gen_spec`-time context, so `set_option veil.smt.* ... in
#check_invariants` silently does not affect solving — a classic footgun
(e.g. believing a sweep runs with a 900 s timeout while it actually uses the
default 60 s). -/
private def warnIfSolverOptionsChangedSinceVCGen (stx : Syntax) (mod : Module) : CommandElabM Unit := do
  let some (genModule, genVals) ← Verifier.solverOptionsAtVCGen.get | return
  unless genModule == mod.name do return
  let curVals := solverRelevantOptionValues (← getOptions)
  let changed := curVals.zip genVals |>.filter fun ((_, cur), (_, gen)) => cur != gen
  unless changed.isEmpty do
    let list := ", ".intercalate <| changed.toList.map
      fun ((n, cur), (_, gen)) => s!"`{n}` (in scope here: {cur}; at VC generation: {gen})"
    logWarningAt stx m!"solver option(s) differ from the values captured when the \
      verification conditions were generated: {list}. Dischargers capture solver \
      options at `#gen_spec`, so values set only around this command do NOT \
      affect solving — set them before `#gen_spec` instead."

/-- Report a failure to build the local pre-simplification infrastructure at
`#gen_spec`. By default (`veil.gen.strictLocalSimp`) this is a hard error:
continuing means every VC re-simplifies the full assembled assertion clump,
degrading `#check_invariants` roughly 10x — and the failure mode (instance
search running out of budget) occurs precisely when the model grows large
enough for the degradation to hurt. -/
private def reportLocalSimpFailure (stx : Syntax) (what : MessageData)
    (ex : Exception) : CommandElabM Unit := do
  let msg := m!"unable to {what}: {ex.toMessageData}\n\n\
    Without it, every verification condition re-simplifies the full assembled \
    assertion clump from scratch, degrading `#check_invariants` roughly 10x \
    on large modules. This failure is usually instance-search budget \
    exhaustion on a large assertion clump; raise the budgets before the \
    failing declaration (and before `#gen_spec`):\n\n  \
    set_option synthInstance.maxHeartbeats 2000000\n  \
    set_option synthInstance.maxSize 4096\n  \
    set_option maxRecDepth 8192\n\n\
    Alternatively, `set_option veil.gen.strictLocalSimp false` downgrades \
    this error to a warning (accepting the degraded performance)."
  if veil.gen.strictLocalSimp.get (← getOptions) then
    throwErrorAt stx msg
  else
    logWarningAt stx msg

private def warnIfNoInvariantsDefined (mod : Module) : CommandElabM Unit := do
  if mod.invariants.isEmpty then
    logWarning "you have not defined any invariants for this specification; did you forget?"

private def warnIfNoActionsDefined (mod : Module) : CommandElabM Unit := do
  if mod.actions.isEmpty then
    logWarning "you have not defined any actions for this specification; did you forget?"

private def throwIfNoInitializerDefined (mod : Module) : CommandElabM Unit := do
  unless mod.procedures.any (·.info matches .initializer) do
    throwError "no `after_init` block has been defined for this specification; every Veil module must have one"

/-- Crystallizes the specification of the module, i.e. it finalizes the set of
`procedures` and `assertions`. The `stx` parameter is the syntax of the command
that triggered the finalization; it is stored for use by `#model_check` when
generating compiled model source. -/
def Module.ensureSpecIsFinalized (mod : Module) (stx : Syntax) : CommandElabM Module := do
  if mod.isSpecFinalized then return mod
  let mod ← mod.ensureStateIsDefined
  throwIfNoInitializerDefined mod
  warnIfNoInvariantsDefined mod
  warnIfNoActionsDefined mod
  let mod ← do
    let mod ← withTraceNode `veil.perf.elaborator.decl.Assumptions (fun _ => return "Assumptions") do
      let (assumptionCmd, mod) ← mod.assembleAssumptions
      elabVeilCommand assumptionCmd
      if !mod.assumptions.isEmpty then
        liftTermElabM do
          mod.tryDefineLocalAbstractEqForTheoryPredicate assembledAssumptionsName assumptionCmd
      try
        liftTermElabM $ mod.simplifyLocalTheoryPropCore assembledAssumptionsName
      catch ex =>
        reportLocalSimpFailure assumptionCmd
          m!"synthesize LocalTheoryProp simplified core for {assembledAssumptionsName}" ex
      return mod
    let mod ← withTraceNode `veil.perf.elaborator.decl.Invariants (fun _ => return "Invariants") do
      let (invariantCmd, mod) ← mod.assembleInvariants
      trace[veil.debug] s!"Elaborating invariants: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic invariantCmd}"
      elabVeilCommand invariantCmd
      if !mod.invariants.isEmpty then
        try
          liftTermElabM $ mod.simplifyLocalRPropCore assembledInvariantsName
        catch ex =>
          reportLocalSimpFailure invariantCmd
            m!"synthesize LocalRProp instance for {assembledInvariantsName}" ex
      if !mod.invariants.isEmpty then
        try
          let localMeetsCmd ← liftTermElabM mod.defineMeetsSpecificationIfSuccessfulAssumingLocalTheorem
          elabVeilCommand localMeetsCmd
        catch ex =>
          reportLocalSimpFailure invariantCmd
            m!"define {localMeetsSpecificationIfSuccessfulAssumingName}" ex
        try
          let localTrMeetsCmd ← liftTermElabM mod.defineTransitionMeetsSpecificationIfSuccessfulAssumingLocalTheorem
          elabVeilCommand localTrMeetsCmd
        catch ex =>
          reportLocalSimpFailure invariantCmd
            m!"define {localTransitionMeetsSpecificationIfSuccessfulAssumingName}" ex
      return mod
    let mod ← withTraceNode `veil.perf.elaborator.decl.Safeties (fun _ => return "Safeties") do
      let (safetyCmd, mod) ← mod.assembleSafeties
      trace[veil.debug] s!"Elaborating safeties: {← liftTermElabM <|Lean.PrettyPrinter.formatTactic safetyCmd}"
      elabVeilCommand safetyCmd
      return mod
    pure mod
  let (labelCmds, mod) ← mod.assembleLabel
  for cmd in labelCmds do
    elabVeilCommand cmd

  -- Generate ActionTag type for symbolic model checking
  -- NOTE: ActionTag is query-local (not a module sort), but we generate the
  -- axiomatisation class and concrete type here for convenience
  let actionNames := mod.actions.map (fun (a : ProcedureSpecification) => Lean.mkIdent a.name)
  if !actionNames.isEmpty then
    let (className, classDecl) ← mkEnumAxiomatisation actionTagType actionNames
    elabVeilCommand classDecl
    for cmd in (← mkEnumConcreteType actionTagType actionNames) do
      elabVeilCommand cmd
    elabVeilCommand $ ← `(open $className:ident)
    -- TODO: Generate equivalence theorem (ActionTag.label_equiv) here

  let mod ← do
    let (nextCmd, mod) ← mod.assembleNext
    elabVeilCommand nextCmd
    let (nextTrCmd, mod) ← mod.assembleNextTransition
    elabVeilCommand nextTrCmd
    let nextTr'Cmd ← mod.assembleNextTransition'
    elabVeilCommand nextTr'Cmd
    try
      if let some abstractNextCmd ← liftTermElabM mod.defineTransitionAbstractForNext then
        elabVeilCommand abstractNextCmd
    catch ex =>
      logWarningAt stx m!"unable to prove {toTransitionAbstractName assembledNextName}: {ex.toMessageData}"
    let (initCmd, mod) ← mod.assembleInit
    elabVeilCommand initCmd
    let (rtsCmd, mod) ← Module.assembleRelationalTransitionSystem mod
    elabVeilCommand rtsCmd
    pure mod
  Verifier.runManager
  -- The manager has been reset for this elaboration; cross-file check
  -- commands later in this file must not reset it again.
  verifierArmedExt.modify fun s => { s with armed := true }
  mod.generateDoesNotThrowVCs
  if ← isNoVerifyMode then
    logInfoAt stx m!"⏭ background doesNotThrow checks not started (veil.noVerify)"
  else
    -- Run doesNotThrow VCs asynchronously and log errors at assertion locations when done
    Verifier.runFilteredAsync Verifier.isDoesNotThrow logDoesNotThrowErrors
  mod.generateInvariantVCs
  -- Persist the VC registry (statements as `Expr`s) for cross-file
  -- checking/proving. Solve-free; deliberately also runs under
  -- `veil.noVerify` — it is exactly what a model-only file needs.
  if veil.gen.vcRegistry.get (← getOptions) then
    mod.persistVCRegistry
  Verifier.solverOptionsAtVCGen.set (some (mod.name, solverRelevantOptionValues (← getOptions)))
  -- Invariant VCs are generated here; verifier commands decide when to start them.
  return { mod with _specFinalizedAt := some stx }

@[command_elab Veil.genSpec]
def elabGenSpec : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.genSpec (fun _ => return "#gen_spec") do
    let mod ← getCurrentModule (errMsg := "You cannot elaborate a specification outside of a Veil module!")
    let mod ← mod.ensureSpecIsFinalized stx
    localEnv.modifyModule (fun _ => mod)

private def proofHasSorryGoalCount (results : VerificationResults VCMetadata SmtResult) : Nat :=
  results.vcs.foldl (init := 0) fun count vc =>
    if vc.proofHasSorry then count + 1 else count

private def trustedSmtWarning (count : Nat) : MessageData :=
  let goalWord := if count == 1 then "goal" else "goals"
  m!"Trusting SMT solver for {count} {goalWord}. `set_option veil.smt.trust false` to enable proof reconstruction."

private def addUndischargedTheoremSuggestion
    (stx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let some theoremText := Verifier.undischargedTheoremStubsText results | return
  let replacement ← match stx.getPos?, stx.getTailPos? with
    | some startPos, some endPos =>
      let commandText := String.Pos.Raw.extract (← getFileMap).source startPos endPos
      pure s!"{commandText}\n\n{theoremText}"
    | _, _ =>
      pure theoremText
  let label := "Insert theorem stubs for undischarged verification conditions"
  let suggestion : Lean.Meta.Tactic.TryThis.Suggestion := {
    suggestion := .string replacement
    toCodeActionTitle? := some fun _ => label
  }
  liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx suggestion
    (header := s!"{label}:\n")

/-- Log verification results asynchronously after all VCs complete. -/
def logVerificationResults (stx : Syntax) (results : VerificationResults VCMetadata SmtResult) : CommandElabM Unit := do
  let msg ← Verifier.formatVerificationResults results
  let violationIsError := veil.violationIsError.get (← getOptions)
  if Verifier.hasFailedVCs results && violationIsError then
    logErrorAt stx msg
  else
    logInfoAt stx msg
  let trustedCount := proofHasSorryGoalCount results
  if trustedCount > 0 then
    logWarningAt stx (trustedSmtWarning trustedCount)
  addUndischargedTheoremSuggestion stx results

private def runFilteredInvariantCheck
    (stx : Syntax)
    (mod : Module)
    (filter : VCMetadata → Bool)
    : CommandElabM Unit := do
  if ← isNoVerifyMode then
    logWarningAt stx m!"⏭ skipped (veil.noVerify): no VCs were solved"
    return
  warnIfSolverOptionsChangedSinceVCGen stx mod
  Verifier.runFilteredAsync filter (logVerificationResults stx)
  Verifier.displayStreamingResults stx
    (do
      -- CAREFUL: do not hold the lock to print
      let mgr ← Verifier.vcManager.atomically fun ref => ref.get
      let done := mgr.isDoneFiltered filter
      let results ← mgr.toResults filter (includeTheoremText := done)
      pure (results, if done then .done else .running))
    mod.specFinalizedAtStx

private def isInductionForAction (actionName : Name) : VCMetadata → Bool
  | .induction m => m.action == actionName
  | .trace _ => false

private def getCheckableAction? (mod : Module) (actionName : Name) : Option ProcedureSpecification :=
  mod.procedures.find? fun proc =>
    proc.name == actionName &&
    match proc.info with
    | .action _ _ => true
    | .initializer | .procedure _ => false

private def throwUnknownCheckAction (mod : Module) (actionName : Name) : CommandElabM α := do
  let availableActions := mod.procedures.filterMap fun proc =>
    match proc.info with
    | .action _ _ => some proc.name.toString
    | .initializer | .procedure _ => none
  let suggestion :=
    if availableActions.isEmpty then
      "This module does not define any actions."
    else
      s!"Available actions: {", ".intercalate availableActions.toList}"
  throwError s!"Unknown action {actionName} for #check_action. {suggestion}"

@[command_elab Veil.checkInvariants]
def elabCheckInvariants : CommandElab := fun stx => do
  -- Use dynamic trace class name for detailed profiling
  withTraceNode `veil.perf.elaborator.checkInvariants (fun _ => return "#check_invariants") do
    -- Skip in compilation mode (no verification feedback needed)
    let mod ← getCurrentModule (errMsg := "You cannot #check_invariant outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    runFilteredInvariantCheck stx mod VCMetadata.isInduction

@[command_elab Veil.checkAction]
def elabCheckAction : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkAction (fun _ => return "#check_action") do
    let mod ← getCurrentModule (errMsg := "You cannot #check_action outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    unless stx.getKind == `Veil.checkAction do
      throwUnsupportedSyntax
    let actionName := stx[1].getId
    unless (getCheckableAction? mod actionName).isSome do
      throwUnknownCheckAction mod actionName
    runFilteredInvariantCheck stx mod (isInductionForAction actionName)

/-! ## Cross-file check/prove commands (persisted VC registry)

These work in any file importing a module compiled with
`veil.gen.vcRegistry`: the module's VCs are re-created in this file's VC
manager from the persisted registry — statements are the persisted `Expr`s,
identical to the defining module's by construction — and discharged here,
under *this* file's solver options (read at tactic runtime; the `#gen_spec`
option-capture rule does not apply on this path). -/

/-- Reset/start the VC manager exactly once per file elaboration for
cross-file commands (mirroring `#gen_spec`'s `runManager`). Subsequent
commands in the same elaboration share the manager — and therefore the VCs
and results — instead of clobbering each other's in-flight work. -/
private def armCrossFileVerifier : CommandElabM Unit := do
  unless (← verifierArmedExt.get).armed do
    Verifier.runManager
    verifierArmedExt.modify fun s => { s with armed := true }

/-- Inside the defining module the in-file commands must be used — the
cross-file form would create a second copy of every VC (the in-file VCs
carry richer metadata, so the idempotence check cannot deduplicate them). -/
private def throwIfInsideDefiningModule (modName : Name) : CommandElabM Unit := do
  if let some mod := (← localEnv.get).currentModule then
    if mod.name == modName then
      throwError "inside `veil module {modName}`, use the in-module form of \
        this command (without the module name); the cross-file form would \
        duplicate the module's VCs"

private def isInductionForCell (actionName propName : Name) : VCMetadata → Bool
  | .induction m => m.action == actionName && m.property == propName
  | .trace _ => false

private def runRegistryFilteredCheck (stx : Syntax) (modName : Name)
    (pred : VCRegistryEntry → Bool) (filter : VCMetadata → Bool)
    : CommandElabM Unit := do
  if ← isNoVerifyMode then
    logWarningAt stx m!"⏭ skipped (veil.noVerify): no VCs were solved"
    return
  throwIfInsideDefiningModule modName
  armCrossFileVerifier
  generateVCsFromRegistry modName pred
  Verifier.runFilteredAsync filter (logVerificationResults stx)
  Verifier.displayStreamingResults stx
    (Verifier.vcManager.atomically fun ref => do
      let mgr ← ref.get
      let results ← mgr.toResults filter
      pure (results, if mgr.isDoneFiltered filter then .done else .running))

@[command_elab Veil.checkInvariantsOf]
def elabCheckInvariantsOf : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkInvariants
      (fun _ => return "#check_invariants (cross-file)") do
    let modName := stx[1].getId
    runRegistryFilteredCheck stx modName (fun _ => true) VCMetadata.isInduction

@[command_elab Veil.checkActionOf]
def elabCheckActionOf : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkAction
      (fun _ => return "#check_action (cross-file)") do
    let modName := stx[1].getId
    let actionName := stx[2].getId
    runRegistryFilteredCheck stx modName (fun e => e.action == actionName)
      (isInductionForAction actionName)

@[command_elab Veil.checkVCOf]
def elabCheckVCOf : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.checkVC
      (fun _ => return "#check_vc (cross-file)") do
    let modName := stx[1].getId
    let actionName := stx[2].getId
    let propName := stx[3].getId
    runRegistryFilteredCheck stx modName
      (fun e => e.action == actionName && e.property == propName)
      (isInductionForCell actionName propName)

/-- Check that the already-persisted theorem `fullName` states exactly the
registry statement `type` (up to defeq), so a manually proven cell cannot
silently drift from what the module's sweep checks. -/
private def checkPreexistingCellTheorem (fullName : Name) (stmtType : Expr) :
    CommandElabM Unit := do
  let some info := (← getEnv).find? fullName
    | throwError "internal error: {fullName} vanished from the environment"
  -- Under Lean 4.32 this must run with the same legacy-defEq discipline
  -- Veil's own generation paths use (`withBackwardsCompatibility` wraps
  -- `elabVeilSolve`/`elabVeilSmt` and the `Simplifier` entry points).
  -- Unshimmed, a statement the in-file sweep accepts is rejected here,
  -- breaking the cross-file path only.
  let ok ← liftTermElabM <| withBackwardsCompatibility <| Meta.isDefEq info.type stmtType
  unless ok do
    throwError "`{fullName}` exists but its statement differs from the \
      module's registry statement for this cell — it cannot be consumed \
      in place of the VC"

@[command_elab Veil.proveAction]
def elabProveAction : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.proveAction
      (fun _ => return "#prove_action") do
    if ← isNoVerifyMode then
      logWarningAt stx m!"⏭ #prove_action skipped (veil.noVerify): no proofs were persisted"
      return
    let modName := stx[1].getId
    let actionName := stx[2].getId
    throwIfInsideDefiningModule modName
    armCrossFileVerifier
    -- Cells whose canonical theorem already exists in the current namespace
    -- (e.g. persisted by a preceding `#prove_vc … by …` — the manual-cell
    -- workflow) are consumed as-is after a statement check, never re-solved.
    let ns ← getCurrNamespace
    let env ← getEnv
    let some allEntries ← getVCRegistry? modName
      | throwError "no VC registry for module `{modName}` in scope \
          (modules with a registry: {(← vcRegistryModules).toList})"
    let preproven := allEntries.filter fun e =>
      e.action == actionName && e.kind == .primary && env.contains (ns.append e.name)
    for e in preproven do
      checkPreexistingCellTheorem (ns.append e.name) e.type
      logInfoAt stx m!"cell ({e.action}, {e.property}): consuming existing \
        `{ns.append e.name}`"
    let skipCells : Std.HashSet (Name × Name) :=
      preproven.foldl (init := {}) fun s e => s.insert (e.action, e.property)
    let pred := fun (e : VCRegistryEntry) =>
      e.action == actionName && !skipCells.contains (e.action, e.property)
    if allEntries.any pred then
      -- Retain witnesses at the dischargers (`veil.gen.streamTheorems`
      -- semantics) so persistence below never re-runs the proof search.
      Command.withScope (fun sc => { sc with opts := veil.gen.streamTheorems.set sc.opts true }) do
        generateVCsFromRegistry modName pred
      let filter := isInductionForAction actionName
      let results ← Verifier.waitFilteredSync filter (persistIncrementally := true)
      Verifier.addProvenTheoremsInDependencyOrder filter
      logVerificationResults stx results
      -- Strict, independent of `veil.violationIsError`: a persistence command
      -- must never let an incomplete theorem set look green.
      if Verifier.hasFailedVCs results then
        throwErrorAt stx "#prove_action {modName} {actionName}: not every VC \
          was proven — the persisted theorem set is incomplete"
    else
      logInfoAt stx m!"#prove_action {modName} {actionName}: every cell was \
        already proven in namespace `{ns}`; nothing to solve"

@[command_elab Veil.proveVC]
def elabProveVC : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.proveVC
      (fun _ => return "#prove_vc") do
    if ← isNoVerifyMode then
      logWarningAt stx m!"⏭ #prove_vc skipped (veil.noVerify): no proof was persisted"
      return
    let modName := stx[1].getId
    let actionName := stx[2].getId
    let propName := stx[3].getId
    throwIfInsideDefiningModule modName
    let some entries ← getVCRegistry? modName
      | throwError "no VC registry for module `{modName}` in scope \
          (modules with a registry: {(← vcRegistryModules).toList})"
    let some e := entries.find? fun e =>
        e.action == actionName && e.property == propName && e.kind == .primary
      | throwError "module `{modName}` has no (action, property) cell \
          ({actionName}, {propName}) in its VC registry"
    let term : Term ←
      if stx[4].isNone then
        e.dischargeTerm modName
      else
        let tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[4][1]⟩
        `(by $tacSeq)
    let fullName := (← getCurrNamespace).append e.name
    let t0 ← IO.monoMsNow
    liftTermElabM <| Term.withDeclName fullName do
      let proof ← Term.elabTermEnsuringType term e.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if proof.hasSorry then
        throwError "#prove_vc {fullName}: the tactic produced a proof containing `sorry`"
      if proof.hasMVar then
        throwError "#prove_vc {fullName}: the proof has unassigned metavariables"
      addDecl (.thmDecl {
        name := fullName, levelParams := []
        «type» := e.type, value := proof })
    let t1 ← IO.monoMsNow
    logInfoAt stx m!"proved cell ({actionName}, {propName}) as {fullName} in {t1 - t0} ms"


@[command_elab Veil.genTheorems]
def elabGenTheorems : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.genTheorems (fun _ => return "#gen_theorems") do
    if ← isNoVerifyMode then
      logWarningAt stx m!"⏭ #gen_theorems skipped (veil.noVerify): no VC theorems were persisted"
      return
    let mod ← getCurrentModule (errMsg := "You cannot #gen_theorems outside of a Veil module!")
    mod.throwIfSpecNotFinalized
    -- UX guard: witness retention (`veil.gen.streamTheorems`) is discharger
    -- behavior, captured at `#gen_spec` — enabling the option only around this
    -- command is inert (§: `solverOptionsAtVCGen` capture semantics).
    if veil.gen.streamTheorems.get (← getOptions) then
      if let some (genModule, genVals) ← Verifier.solverOptionsAtVCGen.get then
        if genModule == mod.name && genVals.contains ("veil.gen.streamTheorems", "false") then
          logWarningAt stx m!"`veil.gen.streamTheorems` is enabled here, but was \
            disabled at `#gen_spec`, where dischargers capture it — witnesses \
            were not retained during the sweep, so theorems will be \
            materialised by serial regeneration. Set the option before \
            `#gen_spec` instead."
    -- Incremental persistence is unconditional: it persists whatever is
    -- already persistable as soon as it (and its upstream) is done, and the
    -- batch pass below covers the rest (stragglers, lazy-dropped witnesses).
    let _ ← Verifier.waitFilteredSync (fun _ => true) (persistIncrementally := true)
    Verifier.addProvenTheoremsInDependencyOrder (fun _ => true)

end Veil
