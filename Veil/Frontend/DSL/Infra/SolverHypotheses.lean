import Lean
import Veil.Base

/-! # Instantiated classes as solver hypotheses

An `instantiate`d class is destructed before every solver call, and each of
its `Prop` fields becomes a hypothesis of the SMT query. That is the
one-line trust statement of the solver-hypothesis set: *every axiom of an
instantiated class is a solver hypothesis*. Two things here keep the
statement one line when a field cannot be translated:

* **`veil_smt_ignore`** withholds a field from the solver
  (`attribute [veil_smt_ignore] C.field`, on the projection function, after
  the class — Lean does not accept attributes on the field itself). The
  field stays a declared axiom of the class, visible to Lean-level
  consumers; the check commands report, once per module, exactly which
  fields are withheld. The statement becomes "every axiom, except the
  listed ones".
* **The first-order check** runs in the check commands before any solver
  starts: every `Prop` field of every instantiated class (flattened through
  parents) is checked for the two binder shapes the SMT translation cannot
  express — a function-typed and a type-typed bound variable — and the first
  offender is reported by class and field, once, instead of an opaque solver
  failure (`Symbol '->' not declared as a type`) on every verification
  condition of the module. -/

open Lean Meta Elab

namespace Veil

/-! ## The `veil_smt_ignore` attribute -/

syntax (name := _root_.veil_smt_ignore) "veil_smt_ignore" : attr

/-- Projection functions of the class fields withheld from the solver. -/
initialize veilSmtIgnoreExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    name := `veil_smt_ignore_ext
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun arrays => arrays.foldl (fun acc a => a.foldl (·.insert ·) acc) {}
  }

/-- Is the class field with projection function `projFn` withheld from the
solver (`veil_smt_ignore`)? -/
def isSmtIgnored (env : Environment) (projFn : Name) : Bool :=
  (veilSmtIgnoreExt.getState env).contains projFn

initialize registerBuiltinAttribute {
  name := `veil_smt_ignore
  descr := "withhold a `Prop` field of a class from the SMT solver when a Veil \
    module `instantiate`s the class (`attribute [veil_smt_ignore] C.field`); \
    the field stays a declared axiom of the class, and the check commands \
    list the withheld fields of every module"
  applicationTime := .afterTypeChecking
  add := fun declName _stx kind => do
    unless kind == AttributeKind.global do
      throwError "`veil_smt_ignore` must be a global attribute"
    let env ← getEnv
    unless (env.getProjectionFnInfo? declName).isSome do
      throwError "`veil_smt_ignore` applies to the projection function of a class \
        field — `attribute [veil_smt_ignore] C.field` after the class — and \
        `{declName}` is not one"
    let info ← getConstInfo declName
    let isPropField ← MetaM.run' <| forallTelescope info.type fun _ body => isProp body
    unless isPropField do
      throwError "`veil_smt_ignore` applies to `Prop` fields (the axioms of a class); \
        `{declName}` is a data field, which is never a solver hypothesis"
    modifyEnv fun env => veilSmtIgnoreExt.addEntry env declName
}

/-! ## Field lookup through parents -/

/-- The projection function that declares field `field` of `structName`,
looking through parent structures (`findField?`), if any. -/
def fieldProjFn? (env : Environment) (structName field : Name) : Option Name := do
  let owner ← findField? env structName field
  getProjFnForField? env owner field

/-- The names `cases` gives the field hypotheses of `hypName : structName`
(`<hyp>.<field>`, or `<hyp>` itself for a single-field structure — see
`Veil.Util.casesMatching`), for the *direct* fields withheld with
`veil_smt_ignore`. Fields of a parent are reached when the parent
projection is destructed in turn. -/
def withheldFieldHypNames (env : Environment) (hypName structName : Name) : Array Name :=
  let fields := getStructureFields env structName
  fields.filterMap fun f =>
    match getProjFnForField? env structName f with
    | some projFn =>
      if isSmtIgnored env projFn then
        some (if fields.size == 1 then hypName else hypName ++ f)
      else none
    | none => none

/-! ## The first-order check -/

/-- The first bound variable in `e` the SMT translation cannot express:
function-typed (a `∀`/`λ`/`∃` over a function or predicate — not an
implication premise, which is a `Prop`), or type-typed (`Sort u`, `u ≠ 0`).
Returns its name and type. Definitions in binder types are unfolded
(`whnf`), so `run : Run state` with `def Run state := Nat → state` is
found. -/
partial def findNonFirstOrderBinder (e : Expr) : MetaM (Option (Name × Expr)) := do
  match e with
  | .forallE .. => forallTelescope e fun xs body => checkBinders xs body
  | .lam .. => lambdaTelescope e fun xs body => checkBinders xs body
  | .letE .. => lambdaLetTelescope e fun xs body => checkBinders xs body
  | .app .. => e.withApp fun f args => do
    if let some r ← findNonFirstOrderBinder f then return some r
    for a in args do
      if let some r ← findNonFirstOrderBinder a then return some r
    return none
  | .mdata _ b => findNonFirstOrderBinder b
  | .proj _ _ b => findNonFirstOrderBinder b
  | _ => return none
where
  checkBinders (xs : Array Expr) (body : Expr) : MetaM (Option (Name × Expr)) := do
    for x in xs do
      let ty ← inferType x
      let ty' ← whnf ty
      if ty'.isForall && !(← isProp ty) then
        return some (← x.fvarId!.getUserName, ty)
      if ty'.isSort && !ty'.isProp then
        return some (← x.fvarId!.getUserName, ty)
      -- A premise may itself hide a higher-order binder (`(h : ∃ f, …) → …`).
      if let some r ← findNonFirstOrderBinder ty then return some r
    findNonFirstOrderBinder body

/-- Analyse one instantiated class `inst : C …` of module `modName`: throw
on the first `Prop` field (flattened through parents) that is neither
first-order nor withheld; return the withheld fields (projection function
names). Non-class hypotheses yield `#[]`. -/
def analyzeInstantiatedClass (modName : Name) (inst : Expr) : MetaM (Array Name) := do
  let ty ← whnf (← inferType inst)
  let some structName := ty.getAppFn.constName? | return #[]
  let env ← getEnv
  unless isStructure env structName do return #[]
  let mut withheld : Array Name := #[]
  for field in getStructureFieldsFlattened env structName (includeSubobjectFields := false) do
    let some projFn := fieldProjFn? env structName field | continue
    let fieldTy ← inferType (← mkProjection inst field)
    unless ← isProp fieldTy do continue
    if isSmtIgnored env projFn then
      withheld := withheld.push projFn
      continue
    if let some (x, xTy) ← findNonFirstOrderBinder fieldTy then
      throwError "the `Prop` field `{projFn}` of instantiated class `{structName}` is not \
        first-order: it binds{indentD m!"{x} : {xTy}"}\nwhich the SMT translation cannot \
        express. Every axiom of an instantiated class is a solver hypothesis, so this would \
        fail every verification condition of module `{modName}` with an opaque solver error. \
        Restate the field in the first-order fragment, or withhold it from the solver with\
        {indentD m!"attribute [veil_smt_ignore] {projFn}"}\nafter the class: it stays a \
        declared axiom of the class, and the check commands list every withheld field of \
        a module."
  return withheld

/-- Modules whose withheld-field report has been logged in this file
elaboration (transient; one info line per module per file). -/
initialize solverHypothesesReportedExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun s n => s.insert n
  }

/-- Log, once per module per file, the fields its instantiated classes
withhold from the solver — the "except" clause of the trust statement.
Silent when nothing is withheld (the statement is then unchanged: every
axiom is a hypothesis). -/
def reportWithheldSolverHypotheses (stx : Syntax) (modName : Name) (withheld : Array Name) :
    Command.CommandElabM Unit := do
  if withheld.isEmpty then return
  if (solverHypothesesReportedExt.getState (← getEnv)).contains modName then return
  modifyEnv fun env => solverHypothesesReportedExt.addEntry env modName
  let list := MessageData.joinSep (withheld.toList.map fun n => m!"`{n}`") ", "
  logInfoAt stx m!"solver hypotheses of module `{modName}`: every `Prop` field of its \
    instantiated classes except the {withheld.size} withheld with `veil_smt_ignore`: {list}"

/-- Run the first-order check on the instance hypotheses `insts` (in a
`MetaM` context where they are fvars) and collect the withheld fields. -/
def analyzeInstantiatedClasses (modName : Name) (insts : Array Expr) : MetaM (Array Name) := do
  let mut withheld : Array Name := #[]
  for inst in insts do
    withheld := withheld ++ (← analyzeInstantiatedClass modName inst)
  return withheld

end Veil
