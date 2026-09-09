import Veil

/-! # Class fields the solver cannot take: the first-order check and `veil_smt_ignore`

Every `Prop` field of an `instantiate`d class is a solver hypothesis. A
field that quantifies over a *function* (here `totality`, over a run
`Nat → state`) is outside the first-order fragment the SMT translation
accepts; without a check, every verification condition of the consuming
module aborts with an opaque solver error that names neither the class nor
the field. The check commands now report the culprit once, by class and
field, before any solver starts (`SIOrchLive.totality` below), and
`attribute [veil_smt_ignore] C.field` withholds a field from the solver —
the field stays a declared axiom of the class, the module verifies, and the
check command lists the withheld fields once per module, so the trust
statement stays one line: every axiom except the listed ones. -/

set_option linter.unusedVariables false

class SIOrchLive (validator slot state : Type) where
  init      : state
  step      : state → state → Prop
  reachable : state → Prop
  opened    : state → validator → slot → Prop
  byz       : validator → Prop
  lt        : slot → slot → Prop
  reachable_init  : reachable init
  reachable_step  : ∀ st st', reachable st → step st st' → reachable st'
  opened_monotone : ∀ st st' i s, step st st' → opened st i s → opened st' i s
  open_prefix_agreement : ∀ st, reachable st →
    ∀ i j s s', ¬ byz i → ¬ byz j →
      opened st i s' → opened st j s → lt s' s → opened st j s'
  -- Totality: quantifies over a RUN, i.e. over a function `Nat → state`.
  -- Deliberately not first-order.
  totality : ∀ (run : Nat → state), run 0 = init → (∀ n, step (run n) (run (n + 1))) →
    ∀ i j s, ¬ byz i → ¬ byz j → (∃ n, opened (run n) i s) → ∃ m, opened (run m) j s

/-! ## Without the attribute: one error, naming class and field -/

veil module SmtIgnoreFieldError

type node
type slot
type ostate

instantiate orch : SIOrchLive node slot ostate

individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

after_init {
  os := orch.init
  appended I S := false
}

action orch_step (os_next : ostate) {
  require orch.step os os_next
  os := os_next
}

action append (i : node) (s : slot) {
  require ¬ orch.byz i
  require orch.opened os i s
  appended i s := true
}

invariant [os_reachable] orch.reachable os
invariant [appended_opened] ∀ i s, appended i s → orch.opened os i s
invariant [prefix_agreement_usable]
  ∀ i j s s', ¬ orch.byz i → ¬ orch.byz j →
    orch.opened os i s' → orch.opened os j s → orch.lt s' s → orch.opened os j s'

#gen_spec

/--
error: the `Prop` field `SIOrchLive.totality` of instantiated class `SIOrchLive` is not first-order: it binds
  run : ℕ → ostate
which the SMT translation cannot express. Every axiom of an instantiated class is a solver hypothesis, so this would fail every verification condition of module `SmtIgnoreFieldError` with an opaque solver error. Restate the field in the first-order fragment, or withhold it from the solver with
  attribute [veil_smt_ignore] SIOrchLive.totality
after the class: it stays a declared axiom of the class, and the check commands list every withheld field of a module.
-/
#guard_msgs (whitespace := lax) in
#check_invariants

end SmtIgnoreFieldError

/-! ## The attribute: on a projection function of a `Prop` field only -/

/-- error: `veil_smt_ignore` applies to `Prop` fields (the axioms of a class); `SIOrchLive.opened` is a data field, which is never a solver hypothesis -/
#guard_msgs in
attribute [veil_smt_ignore] SIOrchLive.opened

/-- error: `veil_smt_ignore` applies to the projection function of a class field — `attribute [veil_smt_ignore] C.field` after the class — and `Nat.succ` is not one -/
#guard_msgs in
attribute [veil_smt_ignore] Nat.succ

attribute [veil_smt_ignore] SIOrchLive.totality

/-! ## With the attribute: the module verifies, and the withheld field is reported -/

veil module SmtIgnoreFieldOk

type node
type slot
type ostate

instantiate orch : SIOrchLive node slot ostate

individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

after_init {
  os := orch.init
  appended I S := false
}

action orch_step (os_next : ostate) {
  require orch.step os os_next
  os := os_next
}

action append (i : node) (s : slot) {
  require ¬ orch.byz i
  require orch.opened os i s
  appended i s := true
}

invariant [os_reachable] orch.reachable os
invariant [appended_opened] ∀ i s, appended i s → orch.opened os i s
invariant [prefix_agreement_usable]
  ∀ i j s s', ¬ orch.byz i → ¬ orch.byz j →
    orch.opened os i s' → orch.opened os j s → orch.lt s' s → orch.opened os j s'

#gen_spec

/--
info: solver hypotheses of module `SmtIgnoreFieldOk`: every `Prop` field of its instantiated classes except the 1 withheld with `veil_smt_ignore`: `SIOrchLive.totality`
---
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  os_reachable ... ✅
  appended_opened ... ✅
  prefix_agreement_usable ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  orch_step
    doesNotThrow ... ✅
    os_reachable ... ✅
    appended_opened ... ✅
    prefix_agreement_usable ... ✅
  append
    doesNotThrow ... ✅
    os_reachable ... ✅
    appended_opened ... ✅
    prefix_agreement_usable ... ✅
-/
#guard_msgs in
#check_invariants

end SmtIgnoreFieldOk

/-! ## Through a parent: the withheld field of an `extends` parent is
withheld when the parent projection is destructed in turn -/

class SIOrchLiveExt (validator slot state : Type) extends SIOrchLive validator slot state where
  opened_reachable : ∀ st i s, opened st i s → reachable st

veil module SmtIgnoreFieldParent

type node
type slot
type ostate

instantiate orch : SIOrchLiveExt node slot ostate

individual os : ostate
relation appended (i : node) (s : slot)

#gen_state

after_init {
  os := orch.init
  appended I S := false
}

action append (i : node) (s : slot) {
  require ¬ orch.byz i
  require orch.opened os i s
  appended i s := true
}

invariant [appended_opened] ∀ i s, appended i s → orch.opened os i s
invariant [appended_reachable] ∀ i s, appended i s → orch.reachable os

#gen_spec

/--
info: solver hypotheses of module `SmtIgnoreFieldParent`: every `Prop` field of its instantiated classes except the 1 withheld with `veil_smt_ignore`: `SIOrchLive.totality`
---
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  appended_opened ... ✅
  appended_reachable ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  append
    doesNotThrow ... ✅
    appended_opened ... ✅
    appended_reachable ... ✅
-/
#guard_msgs in
#check_invariants

end SmtIgnoreFieldParent
