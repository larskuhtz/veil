import Mathlib.Tactic.CasesM
import Mathlib.Tactic.SplitIfs
import Veil.Frontend.DSL.Util
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Util
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.State.SubState
import Veil.Frontend.DSL.State.Interface

/-! # Generated step lemmas

Two-state facts a consumer of a Veil module needs about single actions —
"this action leaves `f` unchanged", "this action only ever sets `f` to
`true`" — and their whole-system consequences, derived at `#gen_spec` from
the actions' pre-computed transitions and kernel-checked. Nothing here is
assumed: the generator inspects each `<action>.ext.tr` body, decides which
lemmas *should* hold, and proves each one; a wrong decision costs a lemma,
never a false theorem. Gated by `veil.gen.stepLemmas`.

## The recognised shape

An imperative action's `tr` body (after `defineTransition`'s simplification)
is a tree of guards, `if`s and `∃`s over *post-state leaves*

    setIn { f₁ := u₁, …, fₙ := uₙ } s₀ = s₁       or       s₀ = s₁

where every `uᵢ` is either the pre-state field `(getFrom s₀).fᵢ` or a
`FieldRepresentation.set descr (…)` of it with `descr` a list literal of
`(pattern, fun x… => value)` pairs. A field is *framed* by an action when
every leaf leaves it unchanged, *monotone* when every leaf leaves it unchanged
or writes the literal `true` (and at least one writes), and *initialised to
`v`* when the initializer's single leaf writes the closed literal `v` at the
all-`none` pattern. Anything else — a `false` write, a computed value, a
`pick`ed value, an action written in `transition` syntax — yields no lemma
for that field (or, for an unrecognised body, for that action).

## What is emitted (module namespace; the transition hypothesis is the only
explicit argument)

* `<action>.frame     : (RTS).tr th s (.<action> args) s' → s'.f₁ = s.f₁ ∧ … ∧ s'.fₖ = s.fₖ`
  (all framed components; one destructuring proof per action)
* `<action>.frame_<f> : (RTS).tr th s (.<action> args) s' → s'.f = s.f` (a projection of it)
* `<action>.mono_<f>  : (RTS).tr th s (.<action> args) s' → ∀ x…, s.f x… = true → s'.f x… = true`
* `<f>.mono           : (RTS).tr th s l s' → ∀ x…, s.f x… = true → s'.f x… = true`
  (when every action has one of the two above, and at least one is `mono`)
* `<f>.init           : (RTS).init th s → ∀ x…, s.f x… = v`
* `<action>.tr_of_step : (RTS).tr th s (.<action> args) s' → <body of <action>.ext.tr>`
  (the exposed transition body, proven once per action and shared by the
  action's lemmas; also what a consumer's hand-written `simp only` produces)

all at the canonical instantiation `relationalTransitionSystem` fixes
(`Theory <sorts>`, `State (FieldAbstractType <sorts>)`). Emission is silent
on success (`trace.veil.stepLemmas` shows the verdicts and timing); a proof
that fails *after* a positive verdict is a warning, because that is a bug in
the script rather than a property of the model. -/

open Lean Elab Command Term Meta

namespace Veil

/-- Whether `#gen_spec` derives the step lemmas (`veil.gen.stepLemmas`). -/
def isStepLemmasEnabled [Monad m] [MonadOptions m] : m Bool := do
  return veil.gen.stepLemmas.get (← getOptions)

/-! ## Detection -/

section Detection

/-- `getFrom s₀`: the pre-state read through the sub-state instance. -/
private def isGetFrom (s₀ e : Expr) : Bool :=
  match_expr e with
  | IsSubStateOf.getFrom _ _ _ x => x == s₀
  | _ => false

private partial def stripLambdas : Expr → Expr
  | .lam _ _ b _ => stripLambdas b
  | e => e

private def isUnitLit (e : Expr) : Bool :=
  e.isConstOf ``PUnit.unit || e.isConstOf ``Unit.unit

/-- The update pattern selects every entry: `(none, …, none, ())`. -/
private partial def isAllNonePattern (e : Expr) : Bool :=
  if isUnitLit e then true else
  match_expr e with
  | Prod.mk _ _ a b => a.isAppOfArity ``Option.none 1 && isAllNonePattern b
  | _ => false

/-- Every element of the update-descriptor list literal writes the literal `true`. -/
private partial def descrAllTrue (descr : Expr) : Bool :=
  match_expr descr with
  | List.nil _ => true
  | List.cons _ hd tl =>
    match_expr hd with
    | Prod.mk _ _ _ v => (stripLambdas v).isConstOf ``Bool.true && descrAllTrue tl
    | _ => false
  | _ => false

/-- A single write at the all-`none` pattern of a literal: that literal. The
literal may mention the module's parameters (`allowed`; a numeral's `OfNat`
instance carries the field's type, which names the sorts) but nothing bound
inside the transition — not the states, not a `pick`ed value. -/
private def descrSingleConst? (allowed : Array FVarId) (descr : Expr) : Option Expr :=
  match_expr descr with
  | List.cons _ hd tl =>
    if !tl.isAppOfArity ``List.nil 1 then none else
    match_expr hd with
    | Prod.mk _ _ pat v =>
      let v := stripLambdas v
      let closed := !v.hasLooseBVars && !v.hasMVar &&
        (collectFVars {} v).fvarIds.all allowed.contains
      if isAllNonePattern pat && closed then some v else none
    | _ => none
  | _ => none

/-- The component is the pre-state field itself: `State.<f> (getFrom s₀)`. -/
private def isUnchanged (proj : Name) (s₀ u : Expr) : Bool :=
  u.isAppOfArity proj 2 && isGetFrom s₀ u.appArg!

/-- The component is the pre-state field with only `true` written into it
(possibly through several nested `set`s). -/
private partial def isSetTrue (proj : Name) (s₀ u : Expr) : Bool :=
  match_expr u with
  | FieldRepresentation.set _ _ _ _ descr fc =>
    (isUnchanged proj s₀ fc || isSetTrue proj s₀ fc) && descrAllTrue descr
  | _ => false

/-- The component is the pre-state field overwritten everywhere by one
literal (closed up to the module's parameters `allowed`): that literal. -/
private def initConst? (allowed : Array FVarId) (proj : Name) (s₀ u : Expr) : Option Expr :=
  match_expr u with
  | FieldRepresentation.set _ _ _ _ descr fc =>
    if isUnchanged proj s₀ fc then descrSingleConst? allowed descr else none
  | _ => none

/-- A post-state leaf: the `State.mk` components under `setIn … s₀ = s₁`, or
`none` for the identity leaf `s₀ = s₁`. -/
private abbrev StepLeaf := Option (Array Expr)

private def leafOf (stateMk : Name) (nFields : Nat) (s₀ x : Expr) : Option (Array StepLeaf) :=
  if x == s₀ then some #[none]
  else match_expr x with
    | IsSubStateOf.setIn _ _ _ st pre =>
      if pre == s₀ && st.isAppOfArity stateMk (nFields + 1) then
        some #[some (st.getAppArgs.extract 1 (nFields + 1))]
      else none
    | _ => none

/-- Collect the post-state leaves of a transition body; `none` when some
conjunct mentioning the post-state is outside the recognised grammar. -/
private partial def collectLeaves (stateMk : Name) (nFields : Nat) (s₀ s₁ : Expr) (e : Expr) :
    MetaM (Option (Array StepLeaf)) := do
  let e := e.consumeMData
  unless e.containsFVar s₁.fvarId! do return some #[]
  let go := collectLeaves stateMk nFields s₀ s₁
  let goLam (f : Expr) : MetaM (Option (Array StepLeaf)) :=
    if f.isLambda then lambdaTelescope f fun _ body => go body else pure none
  let merge (a b : Option (Array StepLeaf)) : Option (Array StepLeaf) := do return (← a) ++ (← b)
  match_expr e with
  | And a b => return merge (← go a) (← go b)
  | ite _ _ _ t f => return merge (← go t) (← go f)
  | dite _ _ _ t f => return merge (← goLam t) (← goLam f)
  | Exists _ p => goLam p
  | Eq _ lhs rhs =>
    if rhs == s₁ then return leafOf stateMk nFields s₀ lhs
    else if lhs == s₁ then return leafOf stateMk nFields s₀ rhs
    else return none
  | _ => return none

/-- Per `State` field (constructor order) of one action. -/
private structure ActionWrites where
  /-- Every leaf leaves the field unchanged. -/
  frame : Array Bool
  /-- Every leaf leaves the field unchanged or writes `true`, and one writes. -/
  mono : Array Bool

/-- Run `k` on the leaves of the transition definition `trName`, with the
module-parameter fvars and the pre-state fvar; `none` when the body is
unrecognised. -/
private def withTransitionLeaves (stateMk : Name) (nFields : Nat) (trName : Name)
    (k : Array FVarId → Expr → Array StepLeaf → MetaM α) : MetaM (Option α) := do
  let some info := (← getEnv).find? trName | return none
  let some val := info.value? | return none
  lambdaTelescope val fun xs body => do
    if xs.size < 3 then return none
    let params := (xs.extract 0 (xs.size - 3)).map (·.fvarId!)
    let s₀ := xs[xs.size - 2]!
    let s₁ := xs[xs.size - 1]!
    let some leaves ← collectLeaves stateMk nFields s₀ s₁ body | return none
    if leaves.isEmpty then return none
    return some (← k params s₀ leaves)

private def analyzeAction (stateFull stateMk : Name) (fields : Array Name) (trName : Name) :
    MetaM (Option ActionWrites) :=
  withTransitionLeaves stateMk fields.size trName fun _ s₀ leaves => do
    let mut frame := #[]
    let mut mono := #[]
    for i in [0:fields.size] do
      let proj := stateFull ++ fields[i]!
      let comp (l : StepLeaf) : Option Expr := l.map (·[i]!)
      let allUnch := leaves.all fun l => match comp l with
        | none => true | some u => isUnchanged proj s₀ u
      let allMono := leaves.all fun l => match comp l with
        | none => true | some u => isUnchanged proj s₀ u || isSetTrue proj s₀ u
      frame := frame.push allUnch
      mono := mono.push (allMono && !allUnch)
    return { frame, mono }

/-- An initial value, abstracted over the module parameters it mentions
(`names`, in abstraction order): re-instantiated against the lemma's own
binders when the statement is built. -/
private structure InitValue where
  value : Expr
  names : Array Name

/-- Per field: the literal the initializer writes everywhere, if any. -/
private def analyzeInitializer (stateFull stateMk : Name) (fields : Array Name) (trName : Name) :
    MetaM (Array (Option InitValue)) := do
  let nothing := fields.map fun _ => (none : Option InitValue)
  let res ← withTransitionLeaves stateMk fields.size trName fun params s₀ leaves => do
    let #[some cs] := leaves | return nothing
    fields.mapIdxM fun i f => do
      let some v := initConst? params (stateFull ++ f) s₀ cs[i]! | return none
      -- A numeral is `@OfNat.ofNat (CanonicalField (toDomain …) (toCodomain …)) n _`:
      -- state it at the reduced type (`ℕ`), which the closing `simp` can see
      -- through at instance transparency.
      let vTy ← inferType v
      let vTy' ← whnfD vTy
      let v := if vTy' == vTy then v else v.replace fun e => if e == vTy then some vTy' else none
      let used := (collectFVars {} v).fvarIds
      let names ← used.mapM (·.getUserName)
      return some { value := v.abstract (used.map mkFVar), names }
  return res.getD nothing

end Detection

/-! ## Generation -/

section Generation

/-- The canonical-representation evaluation set: what a consumer uses by hand
to evaluate the field-representation `get`/`set` pair at the functional
representation. -/
private def canonicalSimpSet : Array Ident := #[
  mkIdent ``Veil.FieldRepresentation.set, mkIdent ``Veil.FieldRepresentation.get,
  mkIdent ``Veil.CanonicalField.set, mkIdent ``Veil.FieldUpdateDescr.fieldUpdate,
  mkIdent ``Veil.FieldUpdatePat.match, mkIdent ``Veil.IteratedArrow.curry,
  mkIdent ``Veil.IteratedArrow.uncurry, mkIdent ``Veil.IteratedProd.patCmp,
  mkIdent ``instIsSubStateOfRefl.setIn_overwrite, mkIdent ``instIsSubStateOfRefl.getFrom_id]

private structure LemmaContext where
  mod : Module
  /-- The binder regime of `relationalTransitionSystem`: sorts and user
  parameters, their `Inhabited` instances, the instantiated classes. -/
  headBinders : Array (TSyntax ``Parser.Term.bracketedBinder)
  theoryT : Term
  stateT : Term
  labelT : Term
  /-- `relationalTransitionSystem <sorts>`. -/
  rts : Term
  th : Ident
  s : Ident
  s' : Ident
  l : Ident
  h : Ident
  hx : Ident
  /-- `State` fields in constructor order, with their declaring components. -/
  fields : Array Name
  comps : Array (Option StateComponent)
  stateFull : Name
  stateMk : Name

/-- A lemma binder name that cannot clash with an action argument and is not
an implementation detail: `__`-prefixed binders are classified as such by
`LocalDeclKind.ofBinderName`, and `subst_vars` skips implementation-detail
hypotheses — which would leave the post-state equation unused. -/
private def lemmaBinderIdent (n : Name) : Ident :=
  mkIdent (Name.mkSimple s!"veil_{n}")

private def mkLemmaContext (mod : Module) : CommandElabM LemmaContext := do
  -- The sorts and user parameters `relationalTransitionSystem` takes, made
  -- implicit: a consumer passes only the transition hypothesis.
  let sortBinders ← mod.parameters.filterMapM fun p => match p.kind with
    | .sort _ | .userParameter => some <$> `(bracketedBinder| {$(mkIdent p.name) : $(p.type)})
    | _ => pure none
  let inhabitedBinders ← mod.assumeForEverySort ``Inhabited
  let userDefinedParams := mod.parameters.filter fun p =>
    p.kind matches .moduleTypeclass .userDefined
  let userDefinedBinders ← userDefinedParams.mapM (·.binder)
  let sorts ← mod.uninterpretedParamIdents
  let theoryT ← mod.theoryStx
  let stateT ← `(term| $stateIdent ($fieldAbstractDispatcher $sorts*))
  let labelT ← mod.labelTypeStx
  let rts ← `(term| $assembledRTS $sorts*)
  let stateFull ← resolveGlobalConstNoOverload stateIdent
  let env ← getEnv
  let stateMk := (getStructureCtor env stateFull).name
  let fields := getStructureFields env stateFull
  let comps := fields.map fun f => mod.mutableComponents.find? (·.name == f)
  return {
    mod, headBinders := sortBinders ++ inhabitedBinders ++ userDefinedBinders,
    theoryT, stateT, labelT, rts,
    th := lemmaBinderIdent `th, s := lemmaBinderIdent `s, s' := lemmaBinderIdent `s',
    l := lemmaBinderIdent `l, h := lemmaBinderIdent `h, hx := lemmaBinderIdent `hx,
    fields, comps, stateFull, stateMk }

/-- Elaborate the statement `mkStmt` builds (inside the binders' scope) under
`binders`, prove it with `proof` and add the theorem `name` in the current
namespace. Throws on any failure; never adds a proof carrying `sorry`. -/
private def addStepTheorem (name : Name) (binders : Array (TSyntax ``Parser.Term.bracketedBinder))
    (mkStmt : TermElabM Term) (proof : Term) : CommandElabM Unit := do
  liftTermElabM do
    let (ty, val) ← Term.elabBinders binders fun vs => do
      let stmt ← mkStmt
      -- `withoutErrToSorry` outside `withSynthesize`: the tactic block runs in
      -- the synthesis epilogue, and its first failure must throw rather than
      -- be logged and admitted.
      let ty ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabType stmt
      let ty ← instantiateMVars ty
      let val ← Term.withoutErrToSorry <| Term.withSynthesize <| Term.elabTermEnsuringType proof ty
      -- Instantiate *after* abstracting: the binders' local-context types
      -- still carry the (assigned) universe metavariables of the instance
      -- binders, and the kernel rejects a declaration containing them.
      return (← instantiateMVars (← mkForallFVars vs ty), ← instantiateMVars (← mkLambdaFVars vs val))
    if ty.hasMVar || val.hasMVar || val.hasSorry then
      throwError "the proof was not completed (statement has metavariables: {ty.hasMVar}; \
        proof has metavariables: {val.hasMVar}; proof was admitted: {val.hasSorry})"
    let _ ← addVeilTheorem name ty val

/-- `{th : Theory …} {s s' : State …}`. -/
private def stateBinders (ctx : LemmaContext) (withPost : Bool := true) :
    CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  let thB ← `(bracketedBinder| {$(ctx.th) : $(ctx.theoryT)})
  let sB ← if withPost then `(bracketedBinder| {$(ctx.s) $(ctx.s') : $(ctx.stateT)})
    else `(bracketedBinder| {$(ctx.s) : $(ctx.stateT)})
  return #[thB, sB]

/-- The action's own arguments, implicit. -/
private def actionArgBinders (actualParams : Array Parameter) :
    CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) :=
  actualParams.mapM fun p => `(bracketedBinder| {$(mkIdent p.name) : $(p.type)})

/-- `(h : (RTS).tr th s (.<action> args) s')`. -/
private def actionTransitionHyp (ctx : LemmaContext) (act : Name) (actualParams : Array Parameter) :
    CommandElabM (TSyntax ``Parser.Term.bracketedBinder) := do
  let ctor := mkIdent (labelTypeName ++ act)
  let args : Array Term := actualParams.map fun p => mkIdent p.name
  `(bracketedBinder| ($(ctx.h) : ($(ctx.rts)).tr $(ctx.th) $(ctx.s) ($ctor $args*) $(ctx.s')))

/-- Expose the action's pre-computed transition body in `h`, through the
action's `tr_of_step` lemma. -/
private def exposeTac (ctx : LemmaContext) (act : Name) : CommandElabM (TSyntax `tactic) := do
  let lem := mkIdent (stepExposureLemmaName act)
  `(tactic| replace $(ctx.h):ident := $lem:ident $(ctx.h):ident)

/-- Walk the body to its post-state leaves (each substitutes the post-state). -/
private def destructTac : CommandElabM (TSyntax `tactic) :=
  `(tactic| repeat' (first | casesm* _ ∧ _, ∃ _, _ | split_ifs at *))

/-- Close a monotonicity/initial-value goal at the canonical representation.
Goal-directed (`simp` on the goal with the given facts), because
`simp_all` also rewrites every guard hypothesis with every other and does
not terminate in reasonable time on actions with many guards; `simp_all`
remains the fallback. -/
private def canonicalCloseTac (facts : Array Ident) : CommandElabM (TSyntax `tactic) := do
  let set := canonicalSimpSet.push (mkIdent ``Option.elim) ++ facts
  let fallback := canonicalSimpSet.push (mkIdent ``Option.elim)
  let fast ← `(tactic| (simp [$[$set:ident],*]; done))
  let slow ← `(tactic| simp_all [$[$fallback:ident],*])
  `(tactic| all_goals (subst_vars; first | $fast:tactic | $slow:tactic))

/-- The relation's domain binders `(x₀ : d₀) … (xₖ : dₖ)`. -/
private def domainBinders (sc : StateComponent) : Array (Ident × Term) :=
  sc.domainTerms.mapIdx fun i d => (lemmaBinderIdent (Name.mkSimple s!"x{i}"), d)

private def forallOver [Monad m] [MonadQuotation m] (xs : Array (Ident × Term)) (body : Term) : m Term :=
  xs.foldrM (init := body) fun (x, d) acc => `(∀ ($x : $d), $acc)

/-- `∀ x…, State.f s x… = true → State.f s' x… = true`. -/
private def monoStatement (ctx : LemmaContext) (f : Name) (xs : Array (Ident × Term)) :
    CommandElabM Term := do
  let proj := mkIdent (stateName ++ f)
  let args : Array Term := xs.map fun (x, _) => x
  let lhs ← `($proj $(ctx.s) $args*)
  let rhs ← `($proj $(ctx.s') $args*)
  forallOver xs (← `($lhs = true → $rhs = true))

private def introTac (ctx : LemmaContext) (xs : Array (Ident × Term)) : CommandElabM (TSyntax `tactic) := do
  let ids : Array Term := (xs.map fun (x, _) => (x : Term)).push ctx.hx
  `(tactic| intro $ids*)

/-- Per action, in one binder scope (the binders are elaborated once, not
once per field — with a dozen instance binders that is most of the cost):

* `<action>.tr_of_step` — from the transition system's step by the action,
  the action's pre-computed transition body at the canonical instantiation,
  `(RTS).tr th s (.<action> args) s' → ⟨body of <action>.ext.tr at th s s'⟩`,
  computed by simplifying the hypothesis type with the transition system's
  definitions and the action's `derived_eq`/`tr` (the `simp only` a consumer
  runs by hand) and proven by `Eq.mp` of the simp proof; every lemma of the
  action starts from it;
* `<action>.frame` — the conjunction `s'.f₁ = s.f₁ ∧ … ∧ s'.fₖ = s.fₖ` over
  the action's framed components, the one destructuring proof per action;
* `<action>.frame_<f>` — one `And` projection of the bundle per framed field.

Throws on the first failure. -/
private def emitActionFrames (ctx : LemmaContext) (act : Name) (actualParams : Array Parameter)
    (framed : Array Name) : CommandElabM Unit := do
  let binders := ctx.headBinders ++ (← stateBinders ctx) ++ (← actionArgBinders actualParams)
    ++ #[← actionTransitionHyp ctx act actualParams]
  let simps : Array Name := #[assembledRTSName, assembledNextName, assembledNextActName,
    toDerivedEqName (toExtName act), toTransitionName (toExtName act)]
  let expose ← exposeTac ctx act
  let destruct ← destructTac
  let close ←
    if framed.size == 1 then `(tactic| exact rfl)
    else
      let rfls : Array Term ← framed.mapM fun _ => `(rfl)
      `(tactic| exact ⟨$rfls,*⟩)
  let bundleProof ← `(by ($expose:tactic; $destruct:tactic; all_goals (subst_vars; $close:tactic)))
  liftTermElabM <| Term.elabBinders binders fun vs => do
    let h := vs.back!
    -- (1) the exposed body
    let hTy ← instantiateMVars (← inferType h)
    let simplify : Veil.Simp.Simplifier := Veil.Simp.simp simps
    let r : Meta.Simp.Result ← simplify hTy
    let exposeVal ← match r.proof? with
      | some p => mkAppM ``Eq.mp #[p, h]
      | none => pure h
    let exposeTy ← instantiateMVars (← mkForallFVars vs r.expr)
    let exposeVal ← instantiateMVars (← mkLambdaFVars vs exposeVal)
    if exposeTy.hasMVar || exposeVal.hasMVar then
      throwError "exposure: the transition body has metavariables"
    let _ ← addVeilTheorem (stepExposureLemmaName act) exposeTy exposeVal
    if framed.isEmpty then return
    -- (2) the frame bundle
    let lctx ← getLCtx
    let some sDecl := lctx.findFromUserName? ctx.s.getId | throwError "frame bundle: no pre-state binder"
    let some s'Decl := lctx.findFromUserName? ctx.s'.getId | throwError "frame bundle: no post-state binder"
    let χ := (← instantiateMVars (← inferType sDecl.toExpr)).appArg!
    let eqs ← framed.mapM fun f => do
      let proj := Lean.mkConst (ctx.stateFull ++ f)
      mkEq (mkApp2 proj χ s'Decl.toExpr) (mkApp2 proj χ sDecl.toExpr)
    let bundleTy := eqs.pop.foldr (fun e acc => mkAnd e acc) eqs.back!
    let bundleVal ← Term.withoutErrToSorry <| Term.withSynthesize <|
      Term.elabTermEnsuringType bundleProof bundleTy
    let bundleVal ← instantiateMVars bundleVal
    if bundleVal.hasMVar || bundleVal.hasSorry then
      throwError "frame bundle: the proof was not completed"
    let bundleName ← addVeilTheorem (stepFrameBundleName act)
      (← instantiateMVars (← mkForallFVars vs bundleTy))
      (← instantiateMVars (← mkLambdaFVars vs bundleVal))
    -- (3) the projections
    let mut cur := mkAppN (Lean.mkConst bundleName) vs
    for i in [0:framed.size] do
      let (proof, rest) ←
        if i + 1 < framed.size then pure (← mkAppM ``And.left #[cur], ← mkAppM ``And.right #[cur])
        else pure (cur, cur)
      let _ ← addVeilTheorem (stepFrameLemmaName act framed[i]!)
        (← instantiateMVars (← mkForallFVars vs eqs[i]!))
        (← instantiateMVars (← mkLambdaFVars vs proof))
      cur := rest

private def emitMonoLemma (ctx : LemmaContext) (act : Name) (actualParams : Array Parameter)
    (f : Name) (sc : StateComponent) : CommandElabM Unit := do
  let xs := domainBinders sc
  let binders := ctx.headBinders ++ (← stateBinders ctx) ++ (← actionArgBinders actualParams)
    ++ #[← actionTransitionHyp ctx act actualParams]
  let stmt ← monoStatement ctx f xs
  let intro ← introTac ctx xs
  let expose ← exposeTac ctx act
  let destruct ← destructTac
  let close ← canonicalCloseTac #[ctx.hx]
  let proof ← `(by ($intro:tactic; $expose:tactic; $destruct:tactic; $close:tactic))
  addStepTheorem (stepMonoLemmaName act f) binders (pure stmt) proof

/-- `<f>.mono` over every label: one case per action, closed by that action's
frame or monotonicity lemma (`kinds`: `true` = frame, `false` = mono). -/
private def emitFieldMonoLemma (ctx : LemmaContext) (f : Name) (sc : StateComponent)
    (kinds : Array (Name × Bool)) : CommandElabM Unit := do
  let xs := domainBinders sc
  let lB ← `(bracketedBinder| {$(ctx.l) : $(ctx.labelT)})
  let hB ← `(bracketedBinder| ($(ctx.h) : ($(ctx.rts)).tr $(ctx.th) $(ctx.s) $(ctx.l) $(ctx.s')))
  let binders := ctx.headBinders ++ (← stateBinders ctx) ++ #[lB, hB]
  let stmt ← monoStatement ctx f xs
  let intro ← introTac ctx xs
  let mut tac ← `(tactic| cases $(ctx.l):ident)
  for (act, isFrame) in kinds do
    let tag := mkIdent act
    let caseTac ←
      if isFrame then
        let frame := mkIdent (stepFrameLemmaName act f)
        `(tactic| case $tag:ident => ($intro:tactic; rw [$frame:ident $(ctx.h):ident]; exact $(ctx.hx)))
      else
        let mono := mkIdent (stepMonoLemmaName act f)
        `(tactic| case $tag:ident => exact $mono:ident $(ctx.h):ident)
    tac ← `(tactic| ($tac:tactic; $caseTac:tactic))
  let proof ← `(by $tac:tactic)
  addStepTheorem (fieldMonoLemmaName f) binders (pure stmt) proof

/-- `<f>.init`: in every initial state, `f` is the literal `v`. -/
private def emitInitLemma (ctx : LemmaContext) (f : Name) (sc : StateComponent) (v : InitValue) :
    CommandElabM Unit := do
  let xs := domainBinders sc
  let proj := mkIdent (stateName ++ f)
  let hB ← `(bracketedBinder| ($(ctx.h) : ($(ctx.rts)).init $(ctx.th) $(ctx.s)))
  let binders := ctx.headBinders ++ (← stateBinders ctx (withPost := false)) ++ #[hB]
  let args : Array Term := xs.map fun (x, _) => x
  -- The literal is an `Expr` over the transition's parameter telescope; its
  -- free variables are re-bound to the lemma's binders of the same name (the
  -- sorts, the instantiated classes) inside the binder scope.
  let mkStmt : TermElabM Term := do
    let lctx ← getLCtx
    let fvars ← v.names.mapM fun n => do
      let some d := lctx.findFromUserName? n
        | throwError "the initial value mentions `{n}`, which the lemma's binders do not provide"
      pure d.toExpr
    let rhs ← Term.exprToSyntax (v.value.instantiateRev fvars)
    forallOver xs (← `($proj $(ctx.s) $args* = $rhs))
  let initTr := mkIdent (toTransitionName (toExtName initializerName))
  let expose ← `(tactic| simp only [$assembledRTS:ident, $assembledInit:ident, $initTr:ident] at $(ctx.h):ident)
  let destruct ← destructTac
  let close ← canonicalCloseTac #[]
  let proof ←
    if xs.isEmpty then `(by ($expose:tactic; $destruct:tactic; $close:tactic))
    else
      let ids : Array Term := xs.map fun (x, _) => (x : Term)
      `(by (intro $ids*; $expose:tactic; $destruct:tactic; $close:tactic))
  addStepTheorem (fieldInitLemmaName f) binders mkStmt proof

/-- Run one emission; a failure after a positive verdict is a warning (it is
a defect of the proof script, not a property of the model). -/
private def attempt (name : Name) (k : CommandElabM Unit) : CommandElabM Bool := do
  let saved := (← get).messages
  try
    k
    trace[veil.stepLemmas] "emitted `{name}`"
    return true
  catch e =>
    -- Whatever the failed attempt logged (an admitted goal reports an error)
    -- is dropped from the user's diagnostics and kept in the trace: the
    -- warning below is the one visible diagnostic for this failure.
    let logged := (← get).messages.toList.drop saved.toList.length
    modify fun st => { st with messages := saved }
    for msg in logged do
      trace[veil.stepLemmas] "`{name}`: diagnostic of the failed attempt: {msg.data}"
    logWarning m!"step lemma `{name}`: the transition record predicts this lemma, but its \
      proof failed — please report this as a Veil bug ({e.toMessageData})"
    return false

/-- Derive and prove the step lemmas of `mod` (see the module docstring).
Called by `#gen_spec` once the transition system is assembled; solver-free,
kernel-checked, silent on success. -/
def Module.emitStepLemmas (mod : Module) : CommandElabM Unit := do
  withTraceNode `veil.perf.elaborator.stepLemmas (fun _ => return "step lemmas") do
  let t0 ← IO.monoMsNow
  let ctx ← try mkLemmaContext mod catch e =>
    trace[veil.stepLemmas] "no step lemmas for `{mod.name}`: {e.toMessageData}"
    return
  -- Per action: `some true` = frame emitted, `some false` = mono emitted.
  let mut perAction : Array (Name × Array (Option Bool)) := #[]
  let mut complete := true
  let mut nFrame : Nat := 0
  let mut nMono : Nat := 0
  let mut nFieldMono : Nat := 0
  let mut nInit : Nat := 0
  for act in mod.actions do
    if act.info.isTransition then
      trace[veil.stepLemmas] "`{act.name}`: transition-syntax action, no lemmas"
      complete := false
      continue
    let writes? ← try
        let trName ← resolveGlobalConstNoOverload (mkIdent (toTransitionName (toExtName act.name)))
        liftTermElabM (analyzeAction ctx.stateFull ctx.stateMk ctx.fields trName)
      catch _ => pure none
    let some writes := writes?
      | trace[veil.stepLemmas] "`{act.name}`: transition body outside the recognised shape, no lemmas"
        complete := false
        continue
    let (_, actualParams) ← mod.declarationAllParams act.name act.declarationKind
    -- The exposed body, the frame bundle and its projections, in one binder
    -- scope (see `emitActionFrames`). If this fails nothing of the action is
    -- usable (the monotonicity lemmas start from the exposed body too).
    let framed := (Array.range ctx.fields.size).filter fun i =>
      writes.frame[i]! && ctx.comps[i]!.isSome
    unless ← attempt (stepFrameBundleName act.name)
        (emitActionFrames ctx act.name actualParams (framed.map (ctx.fields[·]!))) do
      complete := false
      continue
    nFrame := nFrame + framed.size
    let mut kinds : Array (Option Bool) := #[]
    for i in [0:ctx.fields.size] do
      let f := ctx.fields[i]!
      let some sc := ctx.comps[i]!
        | kinds := kinds.push none; continue
      if writes.frame[i]! then
        kinds := kinds.push (some true)
      else if writes.mono[i]! then
        let ok ← attempt (stepMonoLemmaName act.name f) (emitMonoLemma ctx act.name actualParams f sc)
        if ok then nMono := nMono + 1
        kinds := kinds.push (if ok then some false else none)
      else
        trace[veil.stepLemmas] "`{act.name}` / `{f}`: written with a non-`true` value, no lemma"
        kinds := kinds.push none
    perAction := perAction.push (act.name, kinds)
  -- Whole-system monotonicity: every action has a frame or mono lemma, one is mono.
  if complete && !perAction.isEmpty then
    for i in [0:ctx.fields.size] do
      let f := ctx.fields[i]!
      let some sc := ctx.comps[i]! | continue
      let verdicts := perAction.map fun (a, ks) => (a, ks[i]!)
      if verdicts.all (·.2.isSome) && verdicts.any (·.2 == some false) then
        let kinds := verdicts.map fun (a, k) => (a, k.getD true)
        if ← attempt (fieldMonoLemmaName f) (emitFieldMonoLemma ctx f sc kinds) then
          nFieldMono := nFieldMono + 1
  -- Initial values.
  let inits ← try
      let initTr ← resolveGlobalConstNoOverload (mkIdent (toTransitionName (toExtName initializerName)))
      liftTermElabM (analyzeInitializer ctx.stateFull ctx.stateMk ctx.fields initTr)
    catch _ => pure (ctx.fields.map fun _ => none)
  for i in [0:ctx.fields.size] do
    let f := ctx.fields[i]!
    let some sc := ctx.comps[i]! | continue
    let some v := inits[i]!
      | trace[veil.stepLemmas] "initializer / `{f}`: not a single closed-literal write, no lemma"
        continue
    if ← attempt (fieldInitLemmaName f) (emitInitLemma ctx f sc v) then
      nInit := nInit + 1
  let dt := (← IO.monoMsNow) - t0
  trace[veil.stepLemmas] "`{mod.name}`: {nFrame} frame, {nMono} monotonicity, {nFieldMono} \
    whole-system monotonicity, {nInit} initial-value lemma(s) ({dt} ms)"

end Generation

end Veil
