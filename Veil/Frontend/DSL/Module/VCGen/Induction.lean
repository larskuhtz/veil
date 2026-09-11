import Lean
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Util.Meta
import Veil.Core.Tools.Verifier.Server
import Veil.Frontend.DSL.Tactic
-- FIXME: it really doesn't make sense to import this here
import Veil.Core.UI.Verifier.Model
import Veil.Core.UI.Verifier.InductionCounterexample
import Veil.Frontend.DSL.Module.VCGen.Common

/-!
# Induction VC Generation

This module provides VC generation for inductive invariant verification.
It handles the standard invariant preservation VCs for actions and initializers.
-/

open Lean Elab Term Command

namespace Veil

/-! ## Induction-Specific Result Processing -/

/-- Process SMT outputs and build counterexamples for inductive VCs.

NOTE: must not `getCurrentModule` unconditionally — dischargers also run in
files *importing* the module (the cross-file registry commands,
`#check_action <Module> <action>` etc.), where there is no file-local module
state. There the structured counterexample rendering (which needs the
`Module`) is skipped and the raw model is kept. This function also must not
throw on that path: it runs in the async discharger, downstream of the
result `catch` — a throw here would silently kill the discharger task and
hang every awaiter of its VC. -/
private def overallSmtResult [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT MetaM m] (actName : Name) (outputs : Array SmtOutput) : m (Option SmtResult) := do
  let mod? := (← localEnv.get).currentModule
  buildSmtResult outputs (fun sat => do
    sat.filterMapM (fun ce => return ← ce.mapM (fun ce => do
      try
        let some mod := mod?
          | return .some { raw := ce, rawHtml := ← renderSmtModel ce, structuredJson := Json.null }
        let veilModel ← buildCounterexampleExprs ce mod actName
        let structuredJson : Json ← unsafe veilModel.toJson
        return .some { raw := ce, rawHtml := ← renderSmtModel ce, structuredJson := structuredJson }
      catch ex =>
        dbg_trace "Failed to build counterexample; exception: {← ex.toMessageData.toString}"
        return none)))

/-- Create a DischargerResult from SMT outputs for inductive VCs. -/
private def mkDischargerResult [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
    [MonadLiftT (EIO Std.CloseableChannel.Error) m] [MonadLiftT MetaM m]
    (expectedName : Name) (actName : Name)
    (ch : Std.CloseableChannel ((Name × Nat) × Smt.AsyncOutput))
    (data : Witness ⊕ Exception) (time : Nat) : m (DischargerResult SmtResult) := do
  let outputs ← collectSmtOutputs ch expectedName
  let result ← overallSmtResult actName outputs
  match result with
  | .some result => match result with
    | .error exs => return .error exs time
    | .sat _ => return .disproven result time
    | .unknown _ => return .unknown result time
    | .unsat _ => do
      match data with
      | .inl witness => return .proven (some witness) result time
      | _ =>
        let s := "mkDischargerResult: overallSmtResult is unsat, but no witness provided"
        dbg_trace s; throwError s
  | .none =>
    match data with
    | .inl witness => return .proven (some witness) .none time
    | .inr ex =>
      match ← unknownReasonFromException? ex with
      | some reason => return .unknown (.some (.unknown #[reason])) time
      | none => return .error #[(ex, s!"{← ex.toMessageData.toString}")] time

/-! ## VC Discharger -/

/-- Create a discharger for inductive verification conditions.

`attempt > 0` marks a retry discharger (see `veil.smt.retries`): the manager
only schedules it after an earlier attempt of the same VC timed out
(`VerificationCondition.nextDischarger?`). The perturbed solver configuration
is expected to be baked into `term` itself (via `set_option ... in`), so
witness regeneration replays it unchanged. -/
def VCDischarger.fromTerm (term : Term) (actName : Name) (vcStatement : VCStatement)
    (dischargerId : DischargerIdentifier)
    (nameSuffix : String := "")
    (attempt : Nat := 0)
    (ch : Std.Channel (ManagerNotification VCMetadata SmtResult))
    (_cancelTk? : Option IO.CancelToken := none) : CommandElabM (Discharger SmtResult) := do
  let dischargerId :=
    if nameSuffix.isEmpty then dischargerId
    else { dischargerId with name := Name.mkSimple s!"{dischargerId.name.getString!}{nameSuffix}" }
  let env0 ← getEnv
  -- Snapshot the lazy-witness-regen option at discharger-creation time so the
  -- async callback (which runs in a snapshot branch) sees a deterministic value
  -- independent of any later option changes.
  let lazyRegen := veil.lazyWitnessRegen.get (← getOptions)
  -- Streaming theorem persistence (`veil.gen.streamTheorems`): retain
  -- reconstruction witnesses in full so `#gen_theorems` can persist them
  -- incrementally without re-elaboration. Same snapshot discipline.
  let streamPersist := veil.gen.streamTheorems.get (← getOptions)
  -- Same snapshot discipline for the witness-size instrumentation.
  let measureWitness := veil.report.witnessSizes.get (← getOptions)
  -- Lazy witness regen closure: re-elaborates `term` against `vcStatement.type`
  -- and inlines fresh proofs against `env0` (captured here at creation). Small
  -- (a Term + an Environment ref + a VCStatement); stays attached to the
  -- Discharger for the lifetime of `_dischargerResults`. `#gen_theorems` invokes
  -- it to materialize the witness on demand. Built only when
  -- `veil.lazyWitnessRegen` is enabled; otherwise the full witness is retained
  -- in the result and no regeneration is needed.
  let regen? : Option (Lean.Elab.Command.CommandElabM Witness) :=
    if lazyRegen then some <| do
      Lean.Elab.Command.liftTermElabM do
        let witness ← instantiateMVars $ ← withSynthesize (postpone := .no) $
          withoutErrToSorry $ elabTermEnsuringType term (← vcStatement.type)
        let witness ← inlineFreshProofs env0 witness
        if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
          throwError "lazy-regen witness for {dischargerId.name} has unresolved metavariables"
        return witness
    else none
  -- Strip a retained (sorry-free) witness from the value the *promise* gets:
  -- promise consumers only inspect shape/timing, and a resolved promise pins
  -- its value for the lifetime of the discharger node — it would keep every
  -- streaming-retained witness alive long after the incremental persist pass
  -- releases the manager's result slot, silently defeating the release
  -- (observed as ~15+ GB of cold heap on a ~3800-VC reconstruction sweep,
  -- measured on Lean 4.28; not re-measured on 4.32).
  -- The manager's copy keeps the full witness; sorry-carrying witnesses
  -- (trusted mode) are left untouched to preserve the `hasSorry` signal.
  let promiseStrip : DischargerResult SmtResult → DischargerResult SmtResult := fun res =>
    match res with
    | .proven (some w) data t => if w.hasSorry then res else .proven none data t
    | _ => res
  let discharger ← Discharger.fromTermWith term vcStatement dischargerId ch
      (promiseResult := promiseStrip) fun smtCh data time => do
    let data : Witness ⊕ Exception ← match data with
      | .inl witness => do
        let witness ← inlineFreshProofs env0 witness
        -- A throw here is caught by `Discharger.fromTermWith`, which re-invokes
        -- us with the exception (`.inr`); `mkDischargerResult` then throws its
        -- "unsat, but no witness provided" when the solver succeeded but the
        -- tactic still failed, and the fallback error result is published.
        if witness.hasMVar || witness.hasFVar || witness.hasSyntheticSorry then
          throwError "unsolved goals"
        -- Witness-size instrumentation (`veil.report.witnessSizes`):
        -- measure here, where the full witness exists regardless of
        -- `veil.lazyWitnessRegen` (it is sentinel-ized below).
        if measureWitness then
          Verifier.recordWitnessSize dischargerId.name witness
        pure (.inl witness)
      | .inr ex => pure (.inr ex)
    let dischargerResult ← mkDischargerResult dischargerId.name actName smtCh data time
    -- LAZY WITNESS REGEN (gated on `veil.lazyWitnessRegen`, default true):
    -- replace the (~10 MB) witness with a 1-node sentinel.
    -- `addProvenVCTheorem` treats a stored witness containing `sorryAx` as a
    -- sentinel and regenerates via `Discharger.regenWitness?`, so the sentinel
    -- is never used as a real proof — it exists only to preserve the
    -- `witness.hasSorry` signal that drives the trusted-SMT warning. With
    -- `veil.smt.trust = true` the real witness contains `sorryAx`; we mirror
    -- that with a bare `sorryAx` const. With trust off the real witness has no
    -- sorry; we drop it entirely — unless streaming persistence retains it,
    -- in which case the sorry-free stored witness IS the real proof.
    match data, dischargerResult with
    | .inl witness, .proven _ res t =>
      if lazyRegen then
        -- STREAMING PERSISTENCE (`veil.gen.streamTheorems`): retain sorry-free
        -- (reconstruction) witnesses in full — the incremental persist pass at
        -- `#gen_theorems` adds each to the environment as soon as the VC (and
        -- its upstream) is done, then releases this slot. Trusted witnesses
        -- keep the 1-node sentinel regardless.
        let witness? : Option Witness :=
          if witness.hasSorry then some (Lean.mkConst ``sorryAx)
          else if streamPersist then some witness
          else none
        return .proven witness? res t
      else
        return dischargerResult
    | _, _ => return dischargerResult
  return { discharger with attempt := attempt, regenWitness? := regen? }

/-! ## VC Statement Building -/

private def DeclarationKind.assumesInvariantsForInductionVC : DeclarationKind → Bool
  | .procedure .initializer => false
  | _ => true

private def mkInductionPrecondition [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
    (mod : Module) (dependsOn : Std.HashSet Name) (assumesInvariants : Bool) : m Term := do
  if assumesInvariants then
    let (_, invArgs) ← mod.declarationAllBindersArgs assembledInvariantsName
      (.derivedDefinition .invariantLike dependsOn)
    `(term| (@$assembledInvariants $invArgs*))
  else
    `(term| (fun _ _ => $(mkIdent ``True)))

private def mkVCForSpecTheorem [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m]
    [MonadRecDepth m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (propertyName : Name) (actKind : DeclarationKind)
    (specName : Name) (vcName : Name) (vcKind : InductionVCKind)
    (style : VCStyle := .wp) (extraDeps : Std.HashSet Name := {})
    (extraBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[])
    (extraTerms : Array Term := #[]) : m (VCData VCMetadata) := do
  -- FIXME: make all the name-related/parameter functions work with `ext` names
  let assumesInvariants := actKind.assumesInvariantsForInductionVC
  let baseDeps :=
    if assumesInvariants then
      #[actName, assembledAssumptionsName, assembledInvariantsName]
    else
      #[actName, assembledAssumptionsName]
  let dependsOn := extraDeps.insertMany baseDeps
  let (thmBaseParams, thmExtraParams) ← mod.mkDerivedDefinitionsParamsMapFn (pure ·)
    (.derivedDefinition .theoremLike dependsOn)
  -- NOTE: the VCs are stated in terms of `act.ext` (for WP) or `act.ext.tr` (for TR)
  let actionIdent := match style with
    | .wp => toExtName actName
    | .tr => toTransitionName (toExtName actName)
  let ((_, allModArgs), (actBinders, actArgs)) ← mod.declarationSplitBindersArgs actName actKind
  let (_, assArgs) ← mod.declarationAllBindersArgs assembledAssumptionsName
    (.derivedDefinition .assumptionLike dependsOn)
  let preTerm ← mkInductionPrecondition mod dependsOn assumesInvariants
  return {
    name := vcName,
    params := ← (thmBaseParams ++ thmExtraParams).mapM (·.binder),
    statement := ← expandTermMacro $ ← `(term|
      forall? $actBinders* $extraBinders*,
        $(mkIdent specName)
          (@$(mkIdent actionIdent) $allModArgs* $actArgs*)
          (@$assembledAssumptions $assArgs*)
          $preTerm
          $extraTerms:term*
    ),
    metadata := .induction {
      kind := vcKind,
      style := style,
      «action» := actName,
      property := propertyName,
      baseParams := thmBaseParams,
      extraParams := thmExtraParams,
      stmtDerivedFrom := dependsOn
    }
  }

private def mkDoesNotThrowVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m]
    [MonadRecDepth m] [MonadResolveName m] [MonadTrace m] [MonadOptions m]
    [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `doesNotThrow)
    ``VeilM.doesNotThrowAssuming_ex (Name.mkSimple s!"{actName}_doesNotThrow") vcKind
    (extraBinders := #[← `(bracketedBinder| ($exception:ident : ExId))])
    (extraTerms := #[← `(term| $exception:ident)])

private def mkMeetsSpecificationIfSuccessfulClauseVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m] [MonadRecDepth m] [MonadResolveName m]
    [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name)
    (vcKind : InductionVCKind) : m (VCData VCMetadata) := do
  let extraDeps : Std.HashSet Name := {invariantClause}
  let extraTerms := #[← `(term|
    (@$(mkIdent invariantClause)
      $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName (propertyName := invariantClause) actKind
    ``VeilM.meetsSpecificationIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_{invariantClause}") vcKind
    (extraDeps := extraDeps)
    (extraTerms := extraTerms)

private def mkPreservesInvariantsIfSuccessfulVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
    [MonadEnv m] [MonadRecDepth m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `preservesInvariants)
    ``VeilM.preservesInvariantsIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_preservesInvariants") vcKind

private def mkSucceedsAndInvariantsIfSuccessfulVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m]
    [MonadEnv m] [MonadRecDepth m] [MonadResolveName m] [MonadTrace m]
    [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (vcKind : InductionVCKind)
    : m (VCData VCMetadata) := do
  mkVCForSpecTheorem mod actName actKind (propertyName := `succeedsAndPreservesInvariants)
    ``VeilM.succeedsAndPreservesInvariantsAssuming
    (Name.mkSimple s!"{actName}_succeedsAndPreservesInvariants") vcKind

/-- Generate a TR-style (transition-based) VC for checking if an action preserves
an invariant clause. For ordinary actions this is the fallback VC; for actions
defined with `transition`, this is the primary VC. -/
private def mkMeetsSpecificationIfSuccessfulClauseTrVC [Monad m] [MonadMacroAdapter m] [MonadExceptOf Exception m] [AddErrorMessageContext m] [MonadEnv m] [MonadRecDepth m] [MonadResolveName m]
    [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m]
    (mod : Module) (actName : Name) (actKind : DeclarationKind) (invariantClause : Name)
    (vcKind : InductionVCKind) : m (VCData VCMetadata) := do
  let extraDeps : Std.HashSet Name := {invariantClause}
  let extraTerms := #[← `(term|
    (@$(mkIdent invariantClause)
      $(← mod.declarationAllArgs invariantClause (.stateAssertion .invariant))*) )]
  mkVCForSpecTheorem mod actName (propertyName := invariantClause) actKind
    ``Transition.meetsSpecificationIfSuccessfulAssuming
    (Name.mkSimple s!"{actName}_{invariantClause}_tr") vcKind
    (style := .tr) (extraDeps := extraDeps)
    (extraTerms := extraTerms)

/-! ## Module VC Generation -/

/-- Get the list of actions/initializers that need VC generation. -/
private def Module.actsToCheck (mod : Module) : Array ProcedureSpecification :=
  mod.procedures.filter (fun s => match s.info with
    | .action _ _ | .initializer => true
    | .procedure _ => false)

/-- Retry variants of a discharge tactic, per `veil.smt.retries`: attempt `k`
re-runs `tac` with the solver seed set to `k` and the short
`veil.smt.retryTimeout` budget. The perturbed options are baked into the
returned `by` term via `set_option ... in`, so lazy witness regeneration
(`#gen_theorems`) replays exactly the configuration that succeeded. -/
private def mkRetryTerms [Monad m] [MonadQuotation m] [MonadOptions m]
    (tac : TSyntax `tactic) : m (Array (Nat × Term)) := do
  let opts ← getOptions
  let retryTimeout := Syntax.mkNatLit (veil.smt.retryTimeout.get opts)
  (Array.range (veil.smt.retries.get opts)).mapM fun i => do
    let k := i + 1
    let seed := Syntax.mkNatLit k
    let term ← `(term| by
      set_option veil.smt.seed $seed:num in
      set_option veil.smt.timeout $retryTimeout:num in
      $tac:tactic)
    return (k, term)

/-- Add `retryTerms` (from `mkRetryTerms`) as retry dischargers of `vcId`. -/
private def VCManager.addRetryDischargers
    (mgr : VCManager VCMetadata SmtResult) (vcId : VCId) (actName : Name)
    (nameSuffix : String) (retryTerms : Array (Nat × Term))
    : CommandElabM (VCManager VCMetadata SmtResult) :=
  retryTerms.foldlM (init := mgr) fun mgr (k, term) =>
    mgr.mkAddDischarger vcId (VCDischarger.fromTerm term actName
      (nameSuffix := s!"{nameSuffix}_retry{k}") (attempt := k))

/-- The discharger *term* of a WP invariant-preservation cell: the cheap
non-SMT rung (`veil.vc.cheapRung`) in front of the SMT tactic, as one
`first` inside the *existing* discharger's term.

Still one discharger per VC. Rungs of a single VC are sequential *across
tasks* — `VerificationCondition.nextDischarger?` yields nothing while one
is running — so a separate frame discharger would cost a manager
round-trip per cell and grow the array `VCManager.inFlightCount` walks,
for no gain. In the term, the cheap branch parallelises exactly as the
SMT branch does today and keeps the `.dedicated` thread the task already
has, which the fall-through path still needs for the solver's blocking
FFI.

`invFullName` is the invariant's assembled constant (`<mod>.<prop>`):
`veil_solve_frame` resolves it to find the module's `Invariants` and the
conjunct's position in the clump. A name that is not in the environment
gets no rung at all — a plain SMT term beats a rung that can only ever
fail. -/
private def mkWpDischargeTerm [Monad m] [MonadEnv m] [MonadOptions m] [MonadQuotation m]
    (invFullName : Name) (smtTac : TSyntax `tactic) : m Term := do
  if veil.vc.cheapRung.get (← getOptions) && (← getEnv).contains invFullName then
    `(term| by first | veil_solve_frame $(mkIdent invFullName) | $smtTac:tactic)
  else
    `(term| by $smtTac:tactic)

/-- Generate doesNotThrow VCs for all actions.
    These VCs check that actions don't throw exceptions assuming the invariants hold. -/
def Module.generateDoesNotThrowVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpSolve ← `(tactic| veil_solve_wp_doesnotthrow)
  let wpTactic ← `(by $wpSolve:tactic)
  let wpRetries ← mkRetryTerms wpSolve
  -- Prepare VC data outside the lock
  let vcData ← actsToCheck.mapM fun act =>
    return (act, ← mkDoesNotThrowVC mod act.name act.declarationKind InductionVCKind.primary)
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, vc) in vcData do
      let mgr ← ref.get
      let (mgr, vcId) := mgr.addVC vc {} #[]
      let mgr ← mgr.mkAddDischarger vcId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
      let mgr ← mgr.addRetryDischargers vcId act.name "_WP" wpRetries
      ref.set mgr

/-- Generate invariant preservation VCs for all actions × invariant clauses.
    These VCs check that each action preserves each invariant clause. -/
def Module.generateInvariantVCs (mod : Module) : CommandElabM Unit := do
  let actsToCheck := mod.actsToCheck
  let wpSolve ← `(tactic| veil_solve_wp)
  let trSolve ← `(tactic| veil_solve_tr)
  let trTactic ← `(by $trSolve:tactic)
  -- Retry dischargers deliberately carry the SMT tactic alone: a retry is
  -- only ever scheduled after an attempt of the same VC timed out, by
  -- which point the cheap rung has already failed on that cell. Re-running
  -- it would be pure waste, once per retry.
  let wpRetries ← mkRetryTerms wpSolve
  let trRetries ← mkRetryTerms trSolve
  -- Prepare all VC data outside the lock
  let vcData ← actsToCheck.foldlM (init := #[]) fun acc act => do
    let clauseVCs ← mod.checkableInvariants.foldlM (init := #[]) fun acc' invClause => do
      let trPrimary := act.info.isTransition
      let wpVC ← mkMeetsSpecificationIfSuccessfulClauseVC mod act.name
        act.declarationKind invClause.name
        (if trPrimary then InductionVCKind.alternative else InductionVCKind.primary)
      let trVC ← mkMeetsSpecificationIfSuccessfulClauseTrVC mod act.name
        act.declarationKind invClause.name
        (if trPrimary then InductionVCKind.primary else InductionVCKind.alternative)
      -- The cheap rung needs the invariant's name, so the WP term is built
      -- per clause rather than once for the module.
      let wpTactic ← mkWpDischargeTerm (mod.name ++ invClause.name) wpSolve
      return acc'.push (act, wpVC, trVC, trPrimary, wpTactic)
    return acc ++ clauseVCs
  -- Add all VCs atomically
  Verifier.withVCManager fun ref => do
    for (act, wpVC, trVC, trPrimary, wpTactic) in vcData do
      let mgr ← ref.get
      let mgr ←
        if trPrimary then do
          -- Actions written in `transition` syntax should be proved in their
          -- native two-state form first.  The WP VC still exists as the
          -- fallback, but it no longer drives the normal path for these actions.
          let (mgr, trVCId) := mgr.addVC trVC {} #[]
          let mgr ← mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic act.name (nameSuffix := "_TR"))
          let mgr ← mgr.addRetryDischargers trVCId act.name "_TR" trRetries
          let (mgr, wpVCId) := mgr.addAlternativeVC wpVC trVCId #[]
          let mgr ← mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
          mgr.addRetryDischargers wpVCId act.name "_WP" wpRetries
        else do
          -- Ordinary actions keep the existing WP-first behavior.  TR remains a
          -- fallback counterexample/proof route if the WP VC fails.
          let (mgr, wpVCId) := mgr.addVC wpVC {} #[]
          let mgr ← mgr.mkAddDischarger wpVCId (VCDischarger.fromTerm wpTactic act.name (nameSuffix := "_WP"))
          let mgr ← mgr.addRetryDischargers wpVCId act.name "_WP" wpRetries
          let (mgr, trVCId) := mgr.addAlternativeVC trVC wpVCId #[]
          let mgr ← mgr.mkAddDischarger trVCId (VCDischarger.fromTerm trTactic act.name (nameSuffix := "_TR"))
          mgr.addRetryDischargers trVCId act.name "_TR" trRetries
      ref.set mgr

/-- Generate all VCs (both doesNotThrow and invariant preservation). -/
def Module.generateVCs (mod : Module) : CommandElabM Unit := do
  mod.generateDoesNotThrowVCs
  mod.generateInvariantVCs

/-! ## Persistent VC registry (`veil.gen.vcRegistry`) -/

/-- Strip source info (and re-anchor ident raw `Substring`s) from syntax
about to be persisted in the VC registry. The registry's `params`/
`statement` fields are display/stub syntax only — but syntax fresh from
elaboration carries `SourceInfo.original` whose leading/trailing
`Substring`s (and each ident's `rawVal`) reference the **entire source
string**: pickling one such reference embeds the whole file text in the
olean, so the olean's content — and with it lake's content-addressed
import traces, i.e. every importer's up-to-date check — changes on *any*
source edit, comments included. Sanitized syntax is position-free and
depends only on the syntax tree itself. -/
private partial def sanitizePersistedSyntax : Syntax → Syntax
  | .node _ k args => .node .none k (args.map sanitizePersistedSyntax)
  | .atom _ val => .atom .none val
  | .ident _ _ val pre => .ident .none (toString val).toSubstring val pre
  | .missing => .missing

/-- Persist the current VC manager's induction VCs as `mod`'s VC registry
(`vcRegistryExt`): name/action/property/kind/style, the statement syntax
(display/stub use), and the statement elaborated to a closed `Expr` — the
ground truth the cross-file commands check against. Runs at `#gen_spec`
(after VC generation) when `veil.gen.vcRegistry` is enabled.

The statement elaborations are independent (closed statements against the
current environment) and dominate the cost — measured ~62 ms each, i.e.
~8 min *serial* on a ~7600-VC module — so they run in
core-count parallel chunks, joined before the single extension write.
Entry order (VC uid order) is preserved by in-order concatenation. -/
def Module.persistVCRegistry (mod : Module) : CommandElabM Unit := do
  let vcs ← Verifier.withVCManager fun ref => do
    return (← ref.get).nodes.values.toArray
  let vcs := vcs.qsort (·.uid < ·.uid)
  let inductionVCs := vcs.filterMap fun vc =>
    match vc.metadata with
    | .induction m => some (vc, m)
    | .trace _ => none
  let nWorkers := max 1 ((← getNumCores) - 1)
  let chunkSize := max 1 ((inductionVCs.size + nWorkers - 1) / nWorkers)
  let mut chunks : Array (Array _) := #[]
  let mut i := 0
  while i < inductionVCs.size do
    chunks := chunks.push
      (inductionVCs.extract i (min (i + chunkSize) inductionVCs.size))
    i := i + chunkSize
  let mut joins : Array (IO.Promise (Except String (Array VCRegistryEntry))) := #[]
  for chunk in chunks do
    let promise ← IO.Promise.new
    let cancelTk ← IO.CancelToken.new
    let act ← Command.wrapAsyncAsSnapshot (fun () => do
      -- Never let this task die without resolving the promise (cf. the
      -- discharger-totality lesson: an unresolved promise hangs the join).
      try
        let entries ← liftTermElabM <| chunk.mapM fun (vc, m) => do
          let ty ← vc.toVCStatement.type
          return { name := vc.name, «action» := m.action, property := m.property,
                   kind := m.kind, style := m.style,
                   params := vc.params.map (⟨sanitizePersistedSyntax ·⟩),
                   statement := ⟨sanitizePersistedSyntax vc.statement⟩,
                   «type» := ty : VCRegistryEntry }
        promise.resolve (.ok entries)
      catch ex =>
        let msg ← try ex.toMessageData.toString catch _ => pure "<unrenderable exception>"
        promise.resolve (.error msg)) cancelTk
    let task ← (act ()).asTask
    Command.logSnapshotTask { stx? := none, cancelTk? := cancelTk, task }
    joins := joins.push promise
  let mut entries : Array VCRegistryEntry := #[]
  for p in joins do
    match p.result?.get with
    | some (.ok es) => entries := entries ++ es
    | some (.error msg) =>
      throwError "VC registry for `{mod.name}`: statement elaboration failed: {msg}"
    | none =>
      throwError "VC registry for `{mod.name}`: an elaboration task dropped its result"
  modifyEnv fun env => vcRegistryExt.addEntry env (mod.name, entries)
  logInfo m!"VC registry persisted for `{mod.name}`: {entries.size} VCs \
    (`veil.gen.vcRegistry`)"

/-- The metadata a registry entry's re-created VC carries. Deliberately
minimal (no params, no statement-dependency set — those are display/
generation concerns of the defining file); re-created identically on every
call, which is what makes the idempotence check below work. -/
private def VCRegistryEntry.vcMetadata (e : VCRegistryEntry) : VCMetadata :=
  .induction {
    kind := e.kind, style := e.style, «action» := e.action,
    property := e.property, baseParams := #[], extraParams := #[],
    stmtDerivedFrom := {} }

/-- The discharge tactic for a registry entry, mirroring in-file VC
generation. Solver options are read at tactic runtime in the consuming
file — there is no `#gen_spec` option capture on the cross-file path.
Public: `#prove_vc` uses it as the default tactic. -/
def VCRegistryEntry.dischargeTactic (e : VCRegistryEntry) :
    CommandElabM (TSyntax `tactic) := do
  if e.property == `doesNotThrow then `(tactic| veil_solve_wp_doesnotthrow)
  else match e.style with
    | .wp => `(tactic| veil_solve_wp)
    | .tr => `(tactic| veil_solve_tr)

/-- The discharger *term* for a registry entry, i.e. `dischargeTactic`
with the cheap non-SMT rung (`veil.vc.cheapRung`) in front of it where it
applies — the cross-file twin of `mkWpDischargeTerm`. WP cells only: the
rung goes through the local-WP bridge, and a `doesNotThrow` cell has no
invariant to project. Retry dischargers keep the bare tactic.

Public: `#prove_vc` uses it as the default proof term. -/
def VCRegistryEntry.dischargeTerm (modName : Name) (e : VCRegistryEntry) :
    CommandElabM Term := do
  let tac ← e.dischargeTactic
  match e.style with
  | .wp =>
    if e.property == `doesNotThrow then `(by $tac:tactic)
    else mkWpDischargeTerm (modName ++ e.property) tac
  | _ => `(by $tac:tactic)

private def VCRegistryEntry.nameSuffix (e : VCRegistryEntry) : String :=
  match e.style with | .wp => "_WP" | .tr => "_TR"

/-- Re-create a module's VCs in this file's VC manager from the persisted
registry (`veil.gen.vcRegistry`), restricted to entries matching `pred`,
with the same discharger structure as in-file generation (primary +
dormant alternative per cell, retry ladder per `veil.smt.retries`). The
statements are the persisted `Expr`s — identical to what the defining
module's own sweep checks, by construction. Idempotent: cells already in
the manager (by metadata equality) are skipped, so several commands over
the same module in one file share VCs and results. -/
def generateVCsFromRegistry (modName : Name)
    (pred : VCRegistryEntry → Bool) : CommandElabM Unit := do
  let some allEntries ← getVCRegistry? modName
    | throwError "no VC registry for module `{modName}` in scope \
        (modules with a registry: {(← vcRegistryModules).toList}). The \
        defining module must be elaborated with `set_option \
        veil.gen.vcRegistry true` before its `#gen_spec`."
  let entries := allEntries.filter pred
  if entries.isEmpty then
    throwError "no VCs of module `{modName}` match this command"
  -- Group into cells: (action, property) ↦ primary entry + alternatives.
  let cells : Std.HashMap (Name × Name) (Array VCRegistryEntry) :=
    entries.foldl (init := {}) fun m e =>
      m.insert (e.action, e.property) ((m[(e.action, e.property)]?.getD #[]).push e)
  let retriesFor : VCRegistryEntry → CommandElabM (Array (Nat × Term)) :=
    fun e => do mkRetryTerms (← e.dischargeTactic)
  Verifier.withVCManager fun ref => do
    for (_, cellEntries) in cells do
      let primary? := cellEntries.find? (·.kind == .primary)
      let some primary := primary?
        | throwError "VC registry for `{modName}` has a cell with no \
            primary VC: {cellEntries.map (·.name)}"
      let alternatives := cellEntries.filter (·.kind == .alternative)
      let mgr ← ref.get
      -- Idempotence: skip cells whose primary VC already exists.
      if (mgr.findVCByFilter (· == primary.vcMetadata)).isSome then
        continue
      let mkData (e : VCRegistryEntry) : VCData VCMetadata := {
        name := e.name, params := e.params, statement := e.statement,
        typeExpr? := some e.type, metadata := e.vcMetadata }
      let addDischargers (mgr : VCManager VCMetadata SmtResult) (vcId : VCId)
          (e : VCRegistryEntry) : CommandElabM (VCManager VCMetadata SmtResult) := do
        let term ← e.dischargeTerm modName
        let mgr ← mgr.mkAddDischarger vcId
          (VCDischarger.fromTerm term e.action (nameSuffix := e.nameSuffix))
        mgr.addRetryDischargers vcId e.action e.nameSuffix (← retriesFor e)
      let (mgr, primaryId) := mgr.addVC (mkData primary) {} #[]
      let mut mgr ← addDischargers mgr primaryId primary
      for alt in alternatives do
        let (mgr', altId) := mgr.addAlternativeVC (mkData alt) primaryId #[]
        mgr ← addDischargers mgr' altId alt
      ref.set mgr

end Veil
