import Veil.Frontend.DSL.Util
import Veil.Frontend.DSL.Module.Names
import Veil.Frontend.DSL.Module.Syntax
import Veil.Frontend.DSL.Infra.EnvExtensions
import Veil.Frontend.DSL.Action.Semantics.Theorems
import Veil.Core.Tools.ModelChecker.TransitionSystem

/-! # Composition emission

The Veil-side generator that replaces per-project composition scripts:
given an imported module whose
per-action VCs have been persisted as theorems (`#prove_action` in the
per-action proof files), emit

* per action, the **preservation lemma** `step_<action>` (and `init_case`
  for the initializer) — the assembly of one action's per-property cell
  theorems into a single Hoare-triple-shaped fact about the action's
  derived transition (`emitPreservationLemma`, called by `#prove_action`);
* the **`invariants_of_reachable` induction** over the generated
  `RelationalTransitionSystem.reachable`, one case per action, each a
  one-line application of the action's preservation lemma; and
* one named **`reachable_<property>` projection** per invariant conjunct,
  so downstream consumers never index the `Invariants` conjunction
  positionally (`#gen_composition`).

## The canonical instantiation (the load-bearing design point)

The generated composition regime — `Classical`-baked decidability, no
`DecidableEq` binders, every shared instance argument explicit — is not
reconstructed here by elaboration (instance synthesis at this scale
diverges).
Instead it is **extracted from the module's own
`relationalTransitionSystem` elaboration**:

* the RTS constant's telescope *is* the composition binder regime (sorts +
  `Inhabited` + protocol classes; `DecidableEq` is baked as
  `Classical.propDecidable`);
* the RTS value's `tr` field carries the canonical `NextAct` application
  spine; reducing `NextAct <spine> (Label.<action> args)` yields the
  canonical `<action>.ext` application, whose argument list is — by
  generator construction — exactly the telescope instantiation of every
  persisted per-cell VC theorem of that action;
* the `Invariants` definition's body is the declaration-order authority
  for the conjunct list (never an external metadata table).

Everything emitted here goes through `addDecl` — the kernel checks every
composed proof; nothing in this file extends the trust base. -/

open Lean Elab Command Meta

namespace Veil

/-! ## Canonical-instantiation extraction -/

/-- The canonical instantiation of a module's generated definitions,
extracted from the module's own `relationalTransitionSystem` elaboration.
All `Expr`s live in the local context of the RTS telescope `binders`; use
only inside `withCanonicalRTS`'s continuation. -/
structure CanonicalRTS where
  modName : Name
  /-- The RTS telescope fvars — the composition binder regime. -/
  binders : Array Expr
  /-- `@<mod>.relationalTransitionSystem <binders>`. -/
  rtsApp : Expr
  /-- The environment reader type (`<mod>.Theory …`). -/
  ρ : Expr
  /-- The state type (`<mod>.State (<mod>.FieldAbstractType …)`). -/
  σ : Expr
  /-- The label type (`<mod>.Label …`). -/
  lbl : Expr
  /-- The `Veil.Mode` at which actions run (extracted, not assumed). -/
  mode : Expr
  /-- The action result type (extracted, not assumed). -/
  α : Expr
  /-- The canonical `NextAct` application spine (without the label). -/
  nextActSpine : Array Expr
  /-- `@<mod>.Invariants <canonical spine>` : `ρ → σ → Prop`. -/
  invApp : Expr
  /-- The canonical `initializer.ext`(`.tr`) application spine. -/
  initSpine : Array Expr
  /-- The `default` pre-state the initializer transitions from (extracted
  from the RTS `init` field — carries the baked `Inhabited` instance). -/
  defaultState : Expr

/-- Reduce `e` by beta/iota/proj (`whnfCore`) and single-step head unfolding
until its head is the constant `target`. Deterministic (never unfolds past
the target, unlike plain `whnf`). -/
private partial def reduceToHeadConst (target : Name) (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  if e.getAppFn.isConstOf target then
    return e
  match ← unfoldDefinition? e with
  | some e' => reduceToHeadConst target e'
  | none => throwError "cannot reduce{indentExpr e}\nto an application of `{target}`"

/-- Apply `declName` to the values in `byName`, matching its telescope
binders by user name (the generated derived definitions share binder names
by construction). Stops at the first binder without a value. -/
private def instantiateByName (declName : Name) (byName : Std.HashMap Name Expr) :
    MetaM Expr := do
  let info ← getConstInfo declName
  let mut ty := info.type
  let mut args : Array Expr := #[]
  for _ in [0:512] do
    let .forallE n dom body _ := ty | break
    let some v := byName[n]? | break
    unless ← isDefEq (← inferType v) dom do
      throwError "canonical instantiation of `{declName}`: binder `{n}` \
        expects{indentExpr dom}\nbut the extracted value has type\
        {indentExpr (← inferType v)}"
    args := args.push v
    ty := body.instantiate1 v
  return mkAppN (mkConst declName) args

/-- Run `k` with the canonical instantiation of `modName`'s generated
definitions (see `CanonicalRTS`). -/
def withCanonicalRTS (modName : Name) (k : CanonicalRTS → MetaM θ) : MetaM θ := do
  let rtsName := modName ++ assembledRTSName
  let some (.defnInfo rts) := (← getEnv).find? rtsName
    | throwError "no `{rtsName}` in scope — is `{modName}` an imported Veil \
        module elaborated through `#gen_spec`?"
  unless rts.levelParams.isEmpty do
    throwError "`{rtsName}` is universe-polymorphic — unsupported"
  forallTelescope rts.type fun bs resTy => do
    unless resTy.getAppFn.isConstOf ``RelationalTransitionSystem do
      throwError "`{rtsName}` does not produce a `RelationalTransitionSystem`: {resTy}"
    let #[ρ, σ, lbl] := resTy.getAppArgs
      | throwError "unexpected `RelationalTransitionSystem` arity in {resTy}"
    let rtsApp := mkAppN (mkConst rtsName) bs
    let rtsVal ← whnfCore (rts.value.beta bs)
    -- The `tr` field: `fun rd st label st' => (NextAct <spine> label).toTransitionDerived rd st st'`.
    let nextActName := modName ++ assembledNextActName
    let trField ← whnf (← mkProjection rtsVal `tr)
    let (mode, α, nextActSpine) ← lambdaTelescope trField fun ls body => do
      unless ls.size == 4 do
        throwError "unexpected `tr` field shape for `{rtsName}` (expected a \
          4-ary transition lambda):{indentExpr trField}"
      unless body.getAppFn.isConstOf ``VeilM.toTransitionDerived && body.getAppNumArgs == 8 do
        throwError "unexpected `tr` field body for `{rtsName}`:{indentExpr body}"
      let args := body.getAppArgs
      let nextActApp := args[4]!
      unless nextActApp.getAppFn.isConstOf nextActName do
        throwError "the `tr` field of `{rtsName}` does not apply `{nextActName}`:{indentExpr nextActApp}"
      let spine := nextActApp.getAppArgs
      unless spine.back? == some ls[2]! do
        throwError "the `{nextActName}` application does not end in the label binder:{indentExpr nextActApp}"
      pure (args[0]!, args[3]!, spine.pop)
    -- `Invariants` at the canonical spine, via binder-name matching against
    -- `NextAct`'s telescope (both come from the same parameter machinery).
    let nextActInfo ← getConstInfo nextActName
    let byName ← forallTelescope nextActInfo.type fun nbs _ => do
      unless nbs.size ≥ nextActSpine.size do
        throwError "`{nextActName}` telescope is shorter than its extracted application spine"
      let mut m : Std.HashMap Name Expr := {}
      for i in [0:nextActSpine.size] do
        m := m.insert (← nbs[i]!.fvarId!.getUserName) nextActSpine[i]!
      pure m
    let invApp ← instantiateByName (modName ++ assembledInvariantsName) byName
    -- The `init` field: `fun rd st => @initializer.ext.tr <spine> rd default st`.
    let initField ← whnf (← mkProjection rtsVal `init)
    let extTrName := toTransitionName (toExtName (modName ++ `initializer))
    let (initSpine, defaultState) ← lambdaTelescope initField fun ls body => do
      unless ls.size == 2 do
        throwError "unexpected `init` field shape for `{rtsName}`:{indentExpr initField}"
      let body ← reduceToHeadConst extTrName body
      let args := body.getAppArgs
      unless args.size ≥ 3 && args[args.size - 3]! == ls[0]! && args[args.size - 1]! == ls[1]! do
        throwError "unexpected `init` field body for `{rtsName}`:{indentExpr body}"
      let dflt := args[args.size - 2]!
      if ls.any (fun l => dflt.containsFVar l.fvarId!) then
        throwError "the initializer's pre-state depends on the transition \
          points — unsupported `init` shape:{indentExpr body}"
      pure (args.extract 0 (args.size - 3), dflt)
    k { modName, binders := bs, rtsApp, ρ, σ, lbl, mode, α,
        nextActSpine, invApp, initSpine, defaultState }

/-! ## Conjunct walking (the `Invariants` body is the declaration-order authority) -/

/-- Unfold `invApp` (an `@Invariants <spine>` application) and instantiate
its `rd st` binders, yielding the conjunction tree whose leaves are the
per-property applications, in declaration order. -/
private def invariantsConjunction (invApp th st : Expr) : MetaM Expr := do
  let some unfolded ← unfoldDefinition? invApp
    | throwError "cannot unfold the canonical `Invariants` application:{indentExpr invApp}"
  return unfolded.beta #[th, st]

/-- Fold the conjunction tree bottom-up: `leaf` builds each conjunct's
proof, `And.intro` nodes assemble them. -/
private partial def foldConjuncts (conj : Expr) (leaf : Expr → MetaM Expr) : MetaM Expr := do
  if conj.isAppOfArity ``And 2 then
    let a := conj.appFn!.appArg!
    let b := conj.appArg!
    return mkAppN (mkConst ``And.intro) #[a, b, ← foldConjuncts a leaf, ← foldConjuncts b leaf]
  leaf conj

/-- Visit each conjunct with its projection proof out of `proof` (a proof of
the whole conjunction), left to right — declaration order. -/
private partial def forEachConjunct (conj proof : Expr) (k : Expr → Expr → MetaM Unit) :
    MetaM Unit := do
  if conj.isAppOfArity ``And 2 then
    let a := conj.appFn!.appArg!
    let b := conj.appArg!
    forEachConjunct a (mkAppN (mkConst ``And.left) #[a, b, proof]) k
    forEachConjunct b (mkAppN (mkConst ``And.right) #[a, b, proof]) k
  else
    k conj proof

/-- The property name of an `Invariants` conjunct (`<mod>.<prop> …` → `<prop>`). -/
private def propNameOfConjunct (modName : Name) (conj : Expr) : MetaM Name := do
  let .const n _ := conj.getAppFn
    | throwError "conjunct of `{modName}.{assembledInvariantsName}` is not a \
        named property application:{indentExpr conj}"
  let p := n.replacePrefix modName Name.anonymous
  if p == n then
    throwError "conjunct head `{n}` is not under the `{modName}` namespace:{indentExpr conj}"
  return p

/-! ## Statement/proof assembly helpers -/

/-- Remap the first `n` leading `∀`-binders from explicit to implicit (the
sort binders of the RTS telescope — consumers infer them from the
reachability hypothesis, exactly like the hand-rolled compositions did via
implicit section variables). Instance-implicit binders are kept. -/
private def remapLeadingToImplicit : Expr → Nat → Expr
  | e, 0 => e
  | .forallE n d b bi, k + 1 =>
    .forallE n d (remapLeadingToImplicit b k) (if bi == .default then .implicit else bi)
  | e, _ => e

/-- `addDecl` a theorem unless an identically-stated one already exists
(returns `false` then); a differently-stated duplicate is an error. -/
private def addTheoremIdempotent (name : Name) (stmt value : Expr) : MetaM Bool := do
  if (← getEnv).contains name then
    let info ← getConstInfo name
    unless ← isDefEq info.type stmt do
      throwError "`{name}` already exists with a different statement — \
        refusing to overwrite. Existing:{indentExpr info.type}\nEmitting:{indentExpr stmt}"
    return false
  addDecl (.thmDecl { name, levelParams := [], «type» := stmt, value })
  return true

/-- Everything a composition leaf needs: the triple points of the transition
(`r`/`sPos`/`sPrime`), the proofs feeding the bridge lemma, and the canonical
spine at which the persisted cell theorems are instantiated. -/
private structure LeafContext where
  modName : Name
  /-- Namespace holding the persisted cell theorems. -/
  ns : Name
  actionName : Name
  /-- The canonical `.ext` application spine — by generator construction,
  exactly the telescope instantiation of every cell theorem. -/
  spineArgs : Array Expr
  /-- `<action>.ext.derived_eq`, for TR-form cells. -/
  deqName : Name
  r : Expr
  sPos : Expr
  sPrime : Expr
  hassu : Expr
  hpre : Expr
  htr : Expr

/-- Build the proof of one conjunct: instantiate the persisted cell theorem
(`<ns>.<action>_<property>`, or its `_tr` form) at the canonical spine and
run it through the matching bridge lemma. -/
private def cellLeaf (ctx : LeafContext) (conj : Expr) : MetaM Expr := do
  if conj.isConstOf ``True then
    return mkConst ``True.intro
  let p ← propNameOfConjunct ctx.modName conj
  let wpName := ctx.ns ++ Name.mkSimple s!"{ctx.actionName}_{p}"
  let trName := ctx.ns ++ Name.mkSimple s!"{ctx.actionName}_{p}_tr"
  let env ← getEnv
  let thmName ←
    if env.contains wpName then pure wpName
    else if env.contains trName then pure trName
    else throwError "no persisted cell theorem for ({ctx.actionName}, {p}): \
      expected `{wpName}` (or `{trName}`). Persist the action's cells with \
      `#prove_action` (or `#prove_vc`) in this namespace first."
  let thmApp := mkAppN (mkConst thmName) ctx.spineArgs
  -- Loud, early failure if the theorem's telescope drifted from the spine.
  check thmApp
  let thmTy ← inferType thmApp
  if thmTy.getAppFn.isConstOf ``VeilM.meetsSpecificationIfSuccessfulAssuming then
    mkAppM ``VeilM.triple_of_meets
      #[thmApp, ctx.r, ctx.sPos, ctx.sPrime, ctx.hassu, ctx.hpre, ctx.htr]
  else if thmTy.getAppFn.isConstOf ``Transition.meetsSpecificationIfSuccessfulAssuming then
    -- Convert `htr` from the derived-transition form to the `<act>.ext.tr`
    -- form via the action's `derived_eq`, then the TR bridge.
    unless (← getEnv).contains ctx.deqName do
      throwError "`{ctx.deqName}` does not exist — `{ctx.actionName}` is a \
        `transition`-syntax action, whose TR-form cells cannot currently be \
        bridged to the reachability induction (no `derived_eq` is generated \
        for `Transition.toVeilM`-defined actions; see the `Next'` FIXME in \
        `Veil/Frontend/DSL/Module/Util/Assemble.lean`). Rewrite the action \
        in `action` syntax, or prove this cell in its WP form."
    let deqApp := mkAppN (mkConst ctx.deqName) ctx.spineArgs
    let eq ← mkCongrFun (← mkCongrFun (← mkCongrFun deqApp ctx.r) ctx.sPos) ctx.sPrime
    let htr' ← mkEqMP eq ctx.htr
    mkAppM ``Transition.triple_of_meets
      #[thmApp, ctx.r, ctx.sPos, ctx.sPrime, ctx.hassu, ctx.hpre, htr']
  else
    throwError "cell theorem `{thmName}` does not state a \
      `meetsSpecificationIfSuccessfulAssuming` form:{indentExpr thmTy}"

/-! ## The per-action preservation lemma (`#prove_action`'s exported output) -/

/-- Emit `<ns>.step_<action>` (or `<ns>.init_case` for the initializer): the
one lemma per proof file the composition consumes — the action preserves
(the initializer establishes) the assembled `Invariants` conjunction, with
every conjunct discharged by the action's persisted cell theorem through
the bridge lemmas. Idempotent. Called by `#prove_action` after persistence. -/
def emitPreservationLemma (stx : Syntax) (modName actionName : Name) :
    CommandElabM Unit := do
  let ns ← getCurrNamespace
  let isInit := actionName == `initializer
  let lemmaName := ns ++ (if isInit then `init_case else Name.mkSimple s!"step_{actionName}")
  let t0 ← IO.monoMsNow
  let fresh ← liftTermElabM <| withCanonicalRTS modName fun c => do
    let assuTy := fun th => mkAppN (mkConst ``RelationalTransitionSystem.assumptions)
      #[c.ρ, c.σ, c.lbl, c.rtsApp, th]
    if isInit then
      let extName := toExtName (modName ++ `initializer)
      withLocalDeclD `th c.ρ fun th => do
      withLocalDeclD `s c.σ fun s => do
      withLocalDeclD `hassu (assuTy th) fun hassu => do
      let hinitTy := mkAppN (mkConst ``RelationalTransitionSystem.init)
        #[c.ρ, c.σ, c.lbl, c.rtsApp, th, s]
      withLocalDeclD `hinit hinitTy fun hinit => do
        -- `hinit : (RTS …).init th s` is definitionally
        -- `initializer.ext.tr <spine> th default s`; rewrite along
        -- `derived_eq` into the derived-transition form the bridge consumes.
        let deqName := toDerivedEqName extName
        let deqApp := mkAppN (mkConst deqName) c.initSpine
        let eq ← mkCongrFun (← mkCongrFun (← mkCongrFun deqApp th) c.defaultState) s
        let htr ← mkEqMPR eq hinit
        let conj ← invariantsConjunction c.invApp th s
        let body ← foldConjuncts conj <| cellLeaf {
          modName, ns, actionName, spineArgs := c.initSpine, deqName,
          r := th, sPos := c.defaultState, sPrime := s,
          hassu, hpre := mkConst ``True.intro, htr }
        let fvars := c.binders ++ #[th, s, hassu, hinit]
        let stmt := remapLeadingToImplicit
          (← mkForallFVars fvars (mkApp2 c.invApp th s)) c.binders.size
        addTheoremIdempotent lemmaName stmt (← mkLambdaFVars fvars body)
    else
      let extName := toExtName (modName ++ actionName)
      let ctorName := modName ++ labelTypeName ++ actionName
      let cinfo ← getConstInfoCtor ctorName
      unless cinfo.levelParams.isEmpty do
        throwError "`{ctorName}` is universe-polymorphic — unsupported"
      let ctorApp0 := mkAppN (mkConst ctorName) c.lbl.getAppArgs
      forallTelescope (← inferType ctorApp0) fun actArgs _ => do
      let labelExpr := mkAppN ctorApp0 actArgs
      let nextActApp := mkAppN (mkConst (modName ++ assembledNextActName))
        (c.nextActSpine.push labelExpr)
      let extApp ← reduceToHeadConst extName nextActApp
      let spineArgs := extApp.getAppArgs
      unless actArgs.size ≤ spineArgs.size &&
          (spineArgs.extract (spineArgs.size - actArgs.size) spineArgs.size) == actArgs do
        throwError "the canonical `{extName}` application does not end in the \
          action's arguments:{indentExpr extApp}"
      withLocalDeclD `th c.ρ fun th => do
      withLocalDeclD `s1 c.σ fun s1 => do
      withLocalDeclD `s2 c.σ fun s2 => do
      withLocalDeclD `hassu (assuTy th) fun hassu => do
      withLocalDeclD `ih (mkApp2 c.invApp th s1) fun ih => do
      let htrTy := mkAppN (mkConst ``VeilM.toTransitionDerived)
        #[c.mode, c.ρ, c.σ, c.α, extApp, th, s1, s2]
      withLocalDeclD `htr htrTy fun htr => do
        let conj ← invariantsConjunction c.invApp th s2
        let body ← foldConjuncts conj <| cellLeaf {
          modName, ns, actionName, spineArgs, deqName := toDerivedEqName extName,
          r := th, sPos := s1, sPrime := s2, hassu, hpre := ih, htr }
        let fvars := c.binders ++ #[th, s1, s2, hassu, ih] ++ actArgs ++ #[htr]
        let stmt := remapLeadingToImplicit
          (← mkForallFVars fvars (mkApp2 c.invApp th s2)) c.binders.size
        addTheoremIdempotent lemmaName stmt (← mkLambdaFVars fvars body)
  let dt := (← IO.monoMsNow) - t0
  if fresh then
    logInfoAt stx m!"emitted preservation lemma `{lemmaName}` ({dt} ms)"
  else
    logInfoAt stx m!"preservation lemma `{lemmaName}` already exists (statement verified, {dt} ms)"

/-! ## `#gen_composition` -/

/-- Resolve a lemma `#prove_action` emitted (`step_<action>` / `init_case`),
looking through the layouts the file family uses. -/
private def resolveEmittedLemma (ns modName : Name) (base : Name) : MetaM Name := do
  let candidates := #[ns ++ base, ns ++ `Proofs ++ base, modName ++ `Proofs ++ base]
  for c in candidates do
    if (← getEnv).contains c then return c
  throwError "cannot find `{base}` for module `{modName}` (tried \
    {candidates.toList}) — it is emitted by `#prove_action {modName} …` in \
    the action's proof file; import that file (and check the namespace)."

/-- The `#gen_composition <Module>` payload: emit
`<ns>.invariants_of_reachable` (the `reachable` induction over the
per-action preservation lemmas) and one `<ns>.reachable_<property>`
projection per invariant conjunct. -/
def emitComposition (stx : Syntax) (modName : Name) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let t0 ← IO.monoMsNow
  let (iorName, nProj) ← liftTermElabM <| withCanonicalRTS modName fun c => do
    let indInfo ← getConstInfoInduct (modName ++ labelTypeName)
    unless indInfo.levelParams.isEmpty do
      throwError "`{modName ++ labelTypeName}` is universe-polymorphic — unsupported"
    let lblParams := c.lbl.getAppArgs
    let reachAt := fun (th st : Expr) => mkAppN (mkConst ``RelationalTransitionSystem.reachable)
      #[c.ρ, c.σ, c.lbl, c.rtsApp, th, st]
    withLocalDecl `th .implicit c.ρ fun th => do
    withLocalDecl `st .implicit c.σ fun st => do
    withLocalDeclD `h (reachAt th st) fun h => do
      let iorName := ns ++ `invariants_of_reachable
      let outerFVars := c.binders ++ #[th, st, h]
      let stmt := remapLeadingToImplicit
        (← mkForallFVars outerFVars (mkApp2 c.invApp th st)) c.binders.size
      -- motive: fun (s : σ) (_ : reachable th s) => Invariants th s
      let motive ← withLocalDeclD `s c.σ fun s => do
        withLocalDeclD `hr (reachAt th s) fun hr => do
          mkLambdaFVars #[s, hr] (mkApp2 c.invApp th s)
      -- init case: apply `init_case`.
      let initConst ← resolveEmittedLemma ns modName `init_case
      let initMinor ← withLocalDeclD `s c.σ fun s => do
        let haTy := mkAppN (mkConst ``RelationalTransitionSystem.assumptions)
          #[c.ρ, c.σ, c.lbl, c.rtsApp, th]
        withLocalDeclD `ha haTy fun ha => do
        let hiTy := mkAppN (mkConst ``RelationalTransitionSystem.init)
          #[c.ρ, c.σ, c.lbl, c.rtsApp, th, s]
        withLocalDeclD `hi hiTy fun hi => do
          mkLambdaFVars #[s, ha, hi]
            (mkAppN (mkConst initConst) (c.binders ++ #[th, s, ha, hi]))
      -- step case: ∃-elim the label, case on it, apply `step_<action>`.
      let stepMinor ← withLocalDeclD `s1 c.σ fun s1 => do
        withLocalDeclD `s2 c.σ fun s2 => do
        withLocalDeclD `hr (reachAt th s1) fun hr => do
        let hnTy := mkAppN (mkConst ``RelationalTransitionSystem.next)
          #[c.ρ, c.σ, c.lbl, c.rtsApp, th, s1, s2]
        withLocalDeclD `hnext hnTy fun hnext => do
        withLocalDeclD `ih (mkApp2 c.invApp th s1) fun ih => do
          let hassu ← mkAppM ``RelationalTransitionSystem.reachable_assumptions
            #[c.rtsApp, th, s1, hr]
          let p ← withLocalDeclD `l c.lbl fun l => do
            mkLambdaFVars #[l] (mkAppN (mkConst ``RelationalTransitionSystem.tr)
              #[c.ρ, c.σ, c.lbl, c.rtsApp, th, s1, l, s2])
          let target := mkApp2 c.invApp th s2
          let f ← withLocalDeclD `l c.lbl fun l => do
            withLocalDeclD `htr (p.beta #[l]) fun htr => do
              let motive2 ← withLocalDeclD `l' c.lbl fun l' => do
                mkLambdaFVars #[l'] (.forallE `htr (p.beta #[l']) target .default)
              let branches ← indInfo.ctors.toArray.mapM fun ctorName => do
                let actName := ctorName.replacePrefix (modName ++ labelTypeName) Name.anonymous
                let stepConst ← resolveEmittedLemma ns modName (Name.mkSimple s!"step_{actName}")
                let ctorApp0 := mkAppN (mkConst ctorName) lblParams
                forallTelescope (← inferType ctorApp0) fun cargs _ => do
                  let lExpr := mkAppN ctorApp0 cargs
                  withLocalDeclD `htr (p.beta #[lExpr]) fun htr' => do
                    mkLambdaFVars (cargs ++ #[htr']) (mkAppN (mkConst stepConst)
                      (c.binders ++ #[th, s1, s2, hassu, ih] ++ cargs ++ #[htr']))
              let casesName := modName ++ labelTypeName ++ `casesOn
              let casesInfo ← getConstInfo casesName
              let lvls := casesInfo.levelParams.map fun _ => levelZero
              let casesApp := mkAppN (mkConst casesName lvls)
                (lblParams ++ #[motive2, l] ++ branches)
              mkLambdaFVars #[l, htr] (mkApp casesApp htr)
          let exApp := mkAppN (mkConst ``Exists.elim [← getLevel c.lbl])
            #[c.lbl, p, target, hnext, f]
          mkLambdaFVars #[s1, s2, hr, hnext, ih] exApp
      let recName := mkRecName ``RelationalTransitionSystem.reachable
      let recInfo ← getConstInfo recName
      let recLvls := recInfo.levelParams.map fun _ => levelZero
      let recApp := mkAppN (mkConst recName recLvls)
        #[c.ρ, c.σ, c.lbl, c.rtsApp, th, motive, initMinor, stepMinor, st, h]
      let _ ← addTheoremIdempotent iorName stmt (← mkLambdaFVars outerFVars recApp)
      -- Named per-property projections, in declaration order.
      let iorApp := mkAppN (mkConst iorName) outerFVars
      let conj ← invariantsConjunction c.invApp th st
      let nProj ← IO.mkRef (0 : Nat)
      forEachConjunct conj iorApp fun conjunct proof => do
        if conjunct.isConstOf ``True then return
        let pName ← propNameOfConjunct modName conjunct
        let projName := ns ++ Name.mkSimple s!"reachable_{pName}"
        let stmtP := remapLeadingToImplicit
          (← mkForallFVars outerFVars conjunct) c.binders.size
        let _ ← addTheoremIdempotent projName stmtP (← mkLambdaFVars outerFVars proof)
        nProj.modify (· + 1)
      pure (iorName, ← nProj.get)
  let dt := (← IO.monoMsNow) - t0
  logInfoAt stx m!"#gen_composition {modName}: `{iorName}` + {nProj} named \
    `reachable_*` projections ({dt} ms)"

@[command_elab Veil.genComposition]
def elabGenComposition : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.genComposition
      (fun _ => return "#gen_composition") do
    if ← isModelCheckCompileMode then return
    emitComposition stx stx[1].getId

/-! ## `#gen_proof_files` — scaffold the verified-module file family -/

private def camelCase (n : Name) : String :=
  (n.toString.splitOn "_").foldl (init := "") fun acc part => acc ++ part.capitalize

private def proofFileContents (modName modelModule act : Name) : String :=
  s!"import {modelModule}

/-! # `{modName}` proofs — action `{act}`

Scaffolded by `#gen_proof_files {modName}`; yours to edit. Proves every
registered VC of `{act}` cross-file from the module's persisted VC registry
(`veil.gen.vcRegistry`), persists them as kernel-checked theorems in this
file's olean, and emits the per-action preservation lemma consumed by
`Certify.lean`'s `#gen_composition`.

Manual cells go on `#prove_vc {modName} {act} <property> by <tac>` lines
*before* the `#prove_action` — it consumes them as-is after a statement
check. Solver options are read in this file at tactic runtime (no
`#gen_spec` capture applies on the cross-file path). -/

open Veil {modName}

set_option veil.smt.trust false
-- Proof cache: consume entries earlier solves stored (kernel-replayed on
-- hit, `veil.cache.kernelReplay`); store fresh solves for the next rebuild.
set_option veil.cache.proofs true
-- A kernel-replay hit consumes a manual `#prove_vc … by <tac>` cell at the
-- command level and never elaborates the `by` suffix; the unreachable-/
-- unused-tactic linters would flag that (by design here).
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace {modName}.Proofs

#prove_action {modName} {act}

end {modName}.Proofs
"

private def certifyFileContents (modName modelModule : Name) (actions : Array Name) : String :=
  let imports := actions.map fun act =>
    let stem := if act == `initializer then "Init" else camelCase act
    s!"import {modelModule}.Proofs.{stem}"
  let importBlock := "\n".intercalate imports.toList
  s!"{importBlock}

/-! # `{modName}` certificate

Scaffolded by `#gen_proof_files {modName}`; yours to edit. Imports the
per-action proof files and composes their preservation lemmas into
`{modName}.invariants_of_reachable` (+ named `reachable_<property>`
projections). Downstream consumers import this file and nothing heavier. -/

open Veil {modName}

namespace {modName}

#gen_composition {modName}

end {modName}

#print axioms {modName}.invariants_of_reachable
"

/-- The `#gen_proof_files <Module>` payload: write the file family
(`<ModelDir>/<Model>/Proofs/<Action>.lean` + `<ModelDir>/<Model>/Certify.lean`)
next to the module's defining source file. Never overwrites — existing
files are kept (they may carry manual cells). -/
def emitProofFiles (stx : Syntax) (modName : Name) : CommandElabM Unit := do
  let some entries ← getVCRegistry? modName
    | throwError "no VC registry for module `{modName}` in scope \
        (modules with a registry: {(← vcRegistryModules).toList}). The \
        defining module must set `veil.gen.vcRegistry` before `#gen_spec`."
  let mut actions : Array Name := #[]
  for e in entries do
    unless actions.contains e.action do
      actions := actions.push e.action
  let env ← getEnv
  -- The Lean module holding the model (import target of every proof file).
  let modelModule ← match env.getModuleIdxFor? (modName ++ assembledRTSName) with
    | some idx => pure env.header.moduleNames[idx]!
    | none => pure env.mainModule -- running inside the defining file
  -- Locate the package source root: from the current file's path + module
  -- name when they agree (lake/server elaboration), else from the working
  -- directory (e.g. `lake env lean` on a scratch file).
  let modelRel := "/".intercalate (modelModule.components.map (·.toString))
  let curFile := (← read).fileName
  let curRel := "/".intercalate (env.mainModule.components.map (·.toString)) ++ ".lean"
  let familyDir : System.FilePath ←
    if curFile.endsWith curRel then
      pure ⟨(curFile.dropEnd curRel.length).toString ++ modelRel⟩
    else
      let cwdCandidate := (← IO.currentDir) / modelRel
      if ← System.FilePath.pathExists ⟨cwdCandidate.toString ++ ".lean"⟩ then
        pure cwdCandidate
      else
        throwError "#gen_proof_files: cannot locate the package source root — \
          the current file `{curFile}` does not end with its module path \
          `{curRel}`, and `{cwdCandidate}.lean` does not exist under the \
          working directory"
  IO.FS.createDirAll (familyDir / "Proofs")
  let mut created : Array System.FilePath := #[]
  let mut kept : Array System.FilePath := #[]
  let writeIfAbsent := fun (path : System.FilePath) (contents : String) => do
    if ← path.pathExists then pure (Sum.inr path) else do
      IO.FS.writeFile path contents
      pure (Sum.inl path)
  for act in actions do
    let stem := if act == `initializer then "Init" else camelCase act
    let path := familyDir / "Proofs" / s!"{stem}.lean"
    match ← writeIfAbsent path (proofFileContents modName modelModule act) with
    | .inl p => created := created.push p
    | .inr p => kept := kept.push p
  let certPath := familyDir / "Certify.lean"
  match ← writeIfAbsent certPath (certifyFileContents modName modelModule actions) with
  | .inl p => created := created.push p
  | .inr p => kept := kept.push p
  let keptNote := if kept.isEmpty then m!"" else m!", {kept.size} existing file(s) kept"
  logInfoAt stx m!"#gen_proof_files {modName}: {created.size} file(s) created \
    under `{familyDir.toString}`{keptNote}"

@[command_elab Veil.genProofFiles]
def elabGenProofFiles : CommandElab := fun stx => do
  if ← isModelCheckCompileMode then return
  emitProofFiles stx stx[1].getId

/-! ## `#veil_status` — the audit command

The registry + environment walk that turns "what is proven here?" from a
reading exercise (trust-note chains, per-file pins) into a command: per
registry cell, is a statement-matching kernel-checked theorem in scope,
from which Lean module, and on which axioms. Read-only — nothing is added
to the environment and no solver runs, so it is safe anywhere (including
under `veil.noVerify`). -/

/-- What stands in for one registry cell (an (action, property)
obligation) in the current import closure. -/
private inductive CellVerdict where
  /-- A statement-matching constant with a kernel-checked value is in
  scope. `exact` is false when the statement matches definitionally rather
  than bit-identically (manual cells elaborate their hand-written
  statement syntax). The axiom pass downgrades a `found` cell to
  sorry-stubbed if its closure contains `sorryAx`. -/
  | found (thm : Name) (exact : Bool)
  /-- A constant with a canonical cell name exists, but it does not state
  the registry statement — it cannot stand in for the VC. -/
  | drifted (thm : Name)
  /-- A constant with a canonical cell name states the VC but carries no
  kernel-checked value (an `axiom` or `opaque`) — never `real`. -/
  | noValue (thm : Name)
  /-- No constant with any canonical cell name is in scope. -/
  | missing

private structure CellRow where
  «action» : Name
  property : Name
  verdict : CellVerdict

/-- Candidate namespaces for a module's persisted cell theorems, in
resolution order: the current namespace and its `Proofs` child (a
`#veil_status` sitting next to the proofs), the file family's canonical
`<Module>.Proofs`, and `<Module>` itself (in-module `#gen_theorems`
persistence). Mirrors `resolveEmittedLemma`. -/
private def statusNamespaces (ns modName : Name) : Array Name :=
  #[ns, ns ++ `Proofs, modName ++ `Proofs, modName].foldl (init := #[])
    fun a n => if a.contains n then a else a.push n

/-- Order an axiom set for display: the standard axioms first, in their
conventional `#print axioms` order, then everything else alphabetically —
deterministic, so summary lines are `#guard_msgs`-pinnable. -/
private def canonicalAxiomOrder (axs : Array Name) : Array Name :=
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  std.filter axs.contains ++
    (axs.filter (!std.contains ·)).qsort (·.toString < ·.toString)

private def renderAxioms (axs : Array Name) : String :=
  if axs.isEmpty then "(none)"
  else ", ".intercalate ((canonicalAxiomOrder axs).map (·.toString)).toList

/-- The axiom union over `roots`, with the visited set shared across roots
— one walk over the whole closure, the same cost class as a single
`#print axioms` on a top-level composition. -/
private def collectAxiomsUnion (env : Environment) (roots : Array Name) : Array Name :=
  (roots.foldl (init := ({} : CollectAxioms.State)) fun st r =>
    ((CollectAxioms.collect r).run env).run st |>.2).axioms

/-- The exact axiom set of one constant (fresh visited set — the
per-theorem attribution the table and the stub classification need). -/
private def collectAxiomsOf (env : Environment) (root : Name) : Array Name :=
  (((CollectAxioms.collect root).run env).run {}).2.axioms

/-- The `#veil_status <Module>` payload. See the syntax docstring for the
classification and output contract. -/
def reportVeilStatus (stx : Syntax) (modName : Name) (showTable : Bool) : CommandElabM Unit := do
  let some entries ← getVCRegistry? modName
    | throwError "no VC registry for module `{modName}` in scope \
        (modules with a registry: {(← vcRegistryModules).toList}). The \
        defining module must set `veil.gen.vcRegistry` before `#gen_spec`."
  let ns ← getCurrNamespace
  let env ← getEnv
  let nss := statusNamespaces ns modName
  -- Cells in registry (declaration) order; entries of a cell primary-first,
  -- so the WP/TR encoding that drives the normal proof path resolves first
  -- and the other remains the fallback.
  let mut cellKeys : Array (Name × Name) := #[]
  let mut cellMap : Std.HashMap (Name × Name) (Array VCRegistryEntry) := {}
  for e in entries do
    let k := (e.action, e.property)
    unless cellMap.contains k do cellKeys := cellKeys.push k
    cellMap := cellMap.insert k ((cellMap[k]?.getD #[]).push e)
  let rows : Array CellRow ← liftTermElabM <| cellKeys.mapM fun (act, prop) => do
    let cellEntries := cellMap[(act, prop)]!
    let (prim, alt) := cellEntries.partition (·.kind == .primary)
    let mut fallback : Option CellVerdict := none
    for e in prim ++ alt do
      for nsC in nss do
        let n := nsC ++ e.name
        if let some info := env.find? n then
          if !info.hasValue then
            fallback := fallback.getD (.noValue n) |> some
          else if info.type == e.type then
            return { «action» := act, property := prop, verdict := .found n true }
          else if ← Meta.isDefEq info.type e.type then
            return { «action» := act, property := prop, verdict := .found n false }
          else
            fallback := fallback.getD (.drifted n) |> some
    return { «action» := act, property := prop, verdict := fallback.getD .missing }
  -- Axiom pass. One shared walk for the pinned union; per-theorem sets
  -- (a re-walk per cell) only when the table shows them or a non-standard
  -- axiom needs attributing to its cells.
  let foundThms := rows.filterMap fun r =>
    match r.verdict with | .found t _ => some t | _ => none
  let unionAxs := collectAxiomsUnion env foundThms
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let clean := unionAxs.all std.contains
  let perRow : Std.HashMap Name (Array Name) :=
    if showTable || !clean then
      foundThms.foldl (init := {}) fun m t => m.insert t (collectAxiomsOf env t)
    else {}
  let isStubbed := fun (t : Name) => (perRow[t]?.getD #[]).contains ``sorryAx
  let renderRow := fun (r : CellRow) =>
    let cell := s!"{r.action} {r.property}"
    match r.verdict with
    | .found t exact =>
      let status :=
        if isStubbed t then "sorry-stubbed"
        else if exact then "real" else "real (defeq)"
      let src := match env.getModuleIdxFor? t with
        | some idx => (env.header.moduleNames[idx]!).toString
        | none => "(this file)"
      let axs := match perRow[t]? with
        | some a => renderAxioms a
        | none => "—"
      s!"{cell} | {status} | {t} | {src} | {axs}"
    | .drifted t => s!"{cell} | statement-drift | {t} | — | —"
    | .noValue t => s!"{cell} | axiom-stand-in | {t} | — | —"
    | .missing => s!"{cell} | registry-only | — | — | —"
  let isReal := fun (r : CellRow) =>
    match r.verdict with | .found t _ => !isStubbed t | _ => false
  let nReal : Nat := rows.foldl (init := 0) fun n r => if isReal r then n + 1 else n
  if showTable then
    let header := s!"#veil_status {modName} ({rows.size} cells): \
      action property | status | theorem | defined in | axioms"
    logInfoAt stx <| "\n".intercalate (header :: (rows.map renderRow).toList)
  else
    let problems := rows.filter (!isReal ·)
    unless problems.isEmpty do
      logWarningAt stx <| "\n".intercalate
        (s!"#veil_status {modName}: {problems.size} cell(s) without a real \
          theorem in scope:" :: (problems.map renderRow).toList)
  let mut breakdown : Array String := #[]
  let categories : Array (String × (CellVerdict → Bool)) := #[
    ("sorry-stubbed", fun v => match v with | .found t _ => isStubbed t | _ => false),
    ("statement-drift", fun v => match v with | .drifted _ => true | _ => false),
    ("axiom-stand-in", fun v => match v with | .noValue _ => true | _ => false),
    ("registry-only", fun v => match v with | .missing => true | _ => false)]
  for (word, pred) in categories do
    let n := rows.foldl (init := (0 : Nat)) fun n r => if pred r.verdict then n + 1 else n
    if n > 0 then breakdown := breakdown.push s!"{n} {word}"
  let breakdownStr :=
    if breakdown.isEmpty then "" else s!" ({", ".intercalate breakdown.toList})"
  logInfoAt stx m!"#veil_status {modName}: {nReal}/{rows.size} \
    real{breakdownStr}; axioms: {renderAxioms unionAxs}"

@[command_elab Veil.veilStatus]
def elabVeilStatus : CommandElab := fun stx => do
  withTraceNode `veil.perf.elaborator.veilStatus (fun _ => return "#veil_status") do
    if ← isModelCheckCompileMode then return
    let showTable ←
      if stx[2].isNone then pure false
      else if stx[2][0].getId == `table then pure true
      else throwErrorAt stx[2] "expected `table` (or nothing) after the module name"
    reportVeilStatus stx stx[1].getId showTable

end Veil
