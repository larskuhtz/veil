import Veil

/-! # Destructuring instantiated classes with parents before SMT

A module may `instantiate` a class that `extends` a parent. The fast
first-order preparation (`veil_fol !` → `veil_destruct'`) destructs the
instance into its fields with `cases_type*`; the parent arrives as a
projection field (`inst.toParent : Parent …`), itself structure-typed. If
that field is not destructed in turn, it survives as a structure-typed
variable inside otherwise first-order hypotheses and the SMT translation
of every VC of the module aborts with `cannot translate Type`.

`veil_destruct'` must therefore iterate until no structure type appears
that it has not already destructed. This file is the reproduction: the
same consumer against a class with an `extends` parent
(`PCOrchestrator`), and against the same class with the parent's fields
inlined (`PCOrchestratorFlat`). Both must verify with every cell ✅; the
build fails otherwise. -/

set_option linter.unusedVariables false

class PCFaultModel (validator : Type) where
  byz : validator → Prop

/-- A transition-system skeleton, shared by the contracts that extend it. -/
class PCTransitionSystem (state : Type) where
  init : state → Prop
  step : state → state → Prop
  trans : state → state → Prop
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'

/-- A contract that `extends` the skeleton. -/
class PCOrchestrator (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) extends PCTransitionSystem state where
  opened : state → validator → slot → Prop
  opened_mono : ∀ st st' i s, trans st st' → opened st i s → opened st' i s
  open_prefix_agreement : ∀ st, reachable st → ∀ i j s s', ¬ byz i → ¬ byz j →
    opened st i s' → opened st j s → ord.le s' s → s' ≠ s → opened st j s'

/-- The same contract with the skeleton's fields inlined (no `extends`). -/
class PCOrchestratorFlat (validator slot state : Type) [ord : TotalOrder slot]
    (byz : validator → Prop) where
  init : state → Prop
  step : state → state → Prop
  trans : state → state → Prop
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'
  opened : state → validator → slot → Prop
  opened_mono : ∀ st st' i s, trans st st' → opened st i s → opened st' i s
  open_prefix_agreement : ∀ st, reachable st → ∀ i j s s', ¬ byz i → ¬ byz j →
    opened st i s' → opened st j s → ord.le s' s → s' ≠ s → opened st j s'

veil module ParentClassDestruct

type node
type slot
type ostate

instantiate slot_ord : TotalOrder slot
instantiate fm : PCFaultModel node
instantiate orch : PCOrchestrator node slot ostate fm.byz

immutable individual os0 : ostate
individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

assumption [os0_init] orch.init os0

after_init {
  os := os0
  appended I S := false
}

action orch_step (os_next : ostate) {
  require orch.step os os_next
  os := os_next
}

action append (i : node) (s : slot) {
  require ¬ fm.byz i
  require orch.opened os i s
  appended i s := true
}

invariant [os_reachable] orch.reachable os
invariant [appended_opened] ∀ i s, appended i s → orch.opened os i s
invariant [prefix_usable] ∀ i j s s', ¬ fm.byz i → ¬ fm.byz j →
  orch.opened os i s' → orch.opened os j s → slot_ord.le s' s → s' ≠ s → orch.opened os j s'

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  os_reachable ... ✅
  appended_opened ... ✅
  prefix_usable ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  orch_step
    doesNotThrow ... ✅
    os_reachable ... ✅
    appended_opened ... ✅
    prefix_usable ... ✅
  append
    doesNotThrow ... ✅
    os_reachable ... ✅
    appended_opened ... ✅
    prefix_usable ... ✅
-/
#guard_msgs in
#check_invariants

end ParentClassDestruct

veil module ParentClassInlined

type node
type slot
type ostate

instantiate slot_ord : TotalOrder slot
instantiate fm : PCFaultModel node
instantiate orch : PCOrchestratorFlat node slot ostate fm.byz

immutable individual os0 : ostate
individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

assumption [os0_init] orch.init os0

after_init {
  os := os0
  appended I S := false
}

action orch_step (os_next : ostate) {
  require orch.step os os_next
  os := os_next
}

action append (i : node) (s : slot) {
  require ¬ fm.byz i
  require orch.opened os i s
  appended i s := true
}

invariant [os_reachable] orch.reachable os
invariant [appended_opened] ∀ i s, appended i s → orch.opened os i s
invariant [prefix_usable] ∀ i j s s', ¬ fm.byz i → ¬ fm.byz j →
  orch.opened os i s' → orch.opened os j s → slot_ord.le s' s → s' ≠ s → orch.opened os j s'

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  os_reachable ... ✅
  appended_opened ... ✅
  prefix_usable ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  orch_step
    doesNotThrow ... ✅
    os_reachable ... ✅
    appended_opened ... ✅
    prefix_usable ... ✅
  append
    doesNotThrow ... ✅
    os_reachable ... ✅
    appended_opened ... ✅
    prefix_usable ... ✅
-/
#guard_msgs in
#check_invariants

end ParentClassInlined
