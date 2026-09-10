import Veil

/-! # `step_property` registry test — the defining module

A module with two step properties and a persisted VC registry, so that
`VeilTest/StepPropertyRegistry.lean` can prove its cells cross-file
(`#prove_action`, whose registry entries carry the `step` style) and emit the
whole-system exports with `#gen_composition`. -/

set_option linter.unusedVariables false
set_option veil.gen.vcRegistry true

veil module StepRegMod

type node

relation r : node → Bool
relation frozen : node → Bool

#gen_state

after_init {
  r N := false
  frozen N := false
}

action mark (n : node) {
  require ¬ frozen n
  r n := true
}

action reset (n : node) {
  require ¬ frozen n
  r n := false
}

action freeze (n : node) {
  require r n
  frozen n := true
}

invariant [frozen_r] frozen N → r N

step_property [frozen_mono] { frozen N → frozen' N }
step_property [frozen_stays_r] { frozen N → r' N }

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  frozen_r ... ✅
The following set of actions must preserve the invariant, satisfy the step properties, and successfully terminate:
  reset
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    frozen_stays_r ... ✅
  mark
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    frozen_stays_r ... ✅
  freeze
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    frozen_stays_r ... ✅
-/
#guard_msgs in
#check_invariants

end StepRegMod
