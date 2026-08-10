import Lean
open Lean Lean.Elab Lean.Elab.Command

/-!
# `#gen_monitor` — generate a concrete trace-acceptance monitor

Generates the (error-prone) instantiation boilerplate for a model-conformance
monitor of a Veil module elaborated with `veil.gen.executableActions` (so
`<Module>.NextAct.extracted` and `<Module>.initializer.ext.extracted` exist).

    #gen_monitor <Module> into <Namespace>
      sorts s₁, s₂, …, sₖ            -- concrete sorts, in the module's parameter order
      theory <t>                      -- the immutable-config value (`<Module>.Theory` term)
      byz <b>                         -- OPTIONAL: a `ByzNodeSet` instance override

emits, into `<Namespace>`: `Th`, `St`, `Lbl`, `chThy`, `stInhab` (the specialized
`Inhabited St` seed — avoids the pathological `Inhabited (State χ)` search, as
`#model_check` does via `inhabσ`), `cnext`, `cinit`, `initStates`, and
`step : Lbl → St → List (Veil.ExecutionOutcome Int St)`.

With these in hand, a trace-conformance monitor is a fold: start from
`initStates`, and for each recorded label step every live state with `step`,
keeping the successful outcomes — an empty state set means the trace diverged
from the model.

The syntax is `scoped` so that the argument keywords (`sorts`, `theory`,
`byz`, `into`) are not reserved as tokens in every file importing Veil —
`open Veil.GenMonitor` (or `open scoped Veil.GenMonitor`) activates the
command. Additive; the elaborator imports only `Lean` (the emitted code's
Veil names resolve in the user's file, so this file does not pull in the
Veil parser).
-/

namespace Veil.GenMonitor

scoped syntax (name := genMonitorCmd) "#gen_monitor" ident "into" ident
  "sorts" term,* "theory" term ("byz" term)? : command

@[command_elab genMonitorCmd]
def elabGenMonitor : CommandElab := fun stx => do
  let m : Ident := ⟨stx[1]⟩
  let p : Ident := ⟨stx[3]⟩
  let sortTerms : Array Term := (stx[5].getSepArgs).map (fun s => ⟨s⟩)
  let thy : Term := ⟨stx[7]⟩
  let byz? : Option Term := if stx[8].getNumArgs > 0 then some ⟨stx[8][1]⟩ else none
  -- name qualifiers: `mq` = module-qualified, `pq` = target namespace
  let mq (n : Name) : Ident := mkIdent (m.getId ++ n)
  let pq (n : Name) : Ident := mkIdent (p.getId ++ n)
  -- fully-qualified Veil helper names (resolved in the user's file)
  let vMultiExec := mkIdent `Veil.VeilMultiExecM
  let vOutcome := mkIdent `Veil.ExecutionOutcome
  let vValid := mkIdent `Veil.Extract.extractValidStates
  let vAll := mkIdent `Veil.Extract.extractAllOutcomes
  let fmt := mkIdent `Std.Format
  let pTh := pq `Th
  let pSt := pq `St
  let pLbl := pq `Lbl
  let lId := mkIdent `l
  -- cnext / cinit RHS: instance-applied executor / initializer; override `nset`
  -- iff `byz` was given.
  let cnextRhs ← match byz? with
    | some b => `($(mq `NextAct.extracted) (ρ := $pTh) (σ := $pSt) (nset := $b) $sortTerms* $lId)
    | none   => `($(mq `NextAct.extracted) (ρ := $pTh) (σ := $pSt) $sortTerms* $lId)
  let cinitRhs ← match byz? with
    | some b => `($(mq `initializer.ext.extracted) (ρ := $pTh) (σ := $pSt) (nset := $b) $sortTerms*)
    | none   => `($(mq `initializer.ext.extracted) (ρ := $pTh) (σ := $pSt) $sortTerms*)
  let cmds : Array (TSyntax `command) := #[
    ← `(command| abbrev $pTh := $(mq `Theory) $sortTerms*),
    ← `(command| abbrev $pSt := $(mq `State) ($(mq `FieldConcreteType) $sortTerms*)),
    ← `(command| abbrev $pLbl := $(mq `Label) $sortTerms*),
    ← `(command| def $(pq `chThy) : $pTh := $thy),
    ← `(command| def $(pq `stInhab) : Inhabited $pSt := $(mq `instInhabitedStateFieldConcreteType)),
    ← `(command| def $(pq `cnext) ($lId : $pLbl) : $vMultiExec $fmt Int $pTh $pSt Unit := $cnextRhs),
    ← `(command| def $(pq `cinit) : $vMultiExec $fmt Int $pTh $pSt Unit := $cinitRhs),
    ← `(command| def $(pq `initStates) : List $pSt :=
          ($vValid $(pq `cinit) $(pq `chThy) $(pq `stInhab).default).filterMap id),
    ← `(command| def $(pq `step) (st : $pSt) ($lId : $pLbl) : List ($vOutcome Int $pSt) :=
          $vAll ($(pq `cnext) $lId) $(pq `chThy) st)
  ]
  for c in cmds do
    elabCommand c

end Veil.GenMonitor
