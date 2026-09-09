import Veil

/-! # Cross-file solver-hypothesis check — the defining module

A registry-only model (`veil.gen.vcRegistry`, no in-file sweep) that
instantiates a class with a run-quantifying field withheld from the solver
(`veil_smt_ignore`). The consumer half (`VeilTest/SmtIgnoreFieldRegistry.lean`)
runs the cross-file check commands over it. -/

set_option linter.unusedVariables false
set_option veil.gen.vcRegistry true

class SIRegOrch (validator slot state : Type) where
  init      : state
  step      : state → state → Prop
  reachable : state → Prop
  opened    : state → validator → slot → Prop
  byz       : validator → Prop
  reachable_init  : reachable init
  reachable_step  : ∀ st st', reachable st → step st st' → reachable st'
  opened_monotone : ∀ st st' i s, step st st' → opened st i s → opened st' i s
  totality : ∀ (run : Nat → state), run 0 = init → (∀ n, step (run n) (run (n + 1))) →
    ∀ i j s, ¬ byz i → ¬ byz j → (∃ n, opened (run n) i s) → ∃ m, opened (run m) j s

attribute [veil_smt_ignore] SIRegOrch.totality

veil module SIRegMod

type node
type slot
type ostate

instantiate orch : SIRegOrch node slot ostate

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

#gen_spec

end SIRegMod
