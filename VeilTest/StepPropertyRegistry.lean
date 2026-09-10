import VeilTest.StepPropertyBase

/-! # `step_property` registry test — the cross-file consumer

The step cells travel through the persistent VC registry with their own
discharge style: `#check_action` re-checks them, `#prove_action` persists
them as kernel-checked theorems next to the invariant cells, and
`#gen_composition` emits `<property>_step` (over every label, from the
invariants) and `reachable_<property>_step` (along every step from a
reachable state) besides the usual `invariants_of_reachable`. -/

set_option linter.unusedVariables false

open Veil StepRegMod

set_option veil.smt.trust false

-- The step cells travel through the registry with their `step` style and
-- are re-checked by the action-level command like any other cell.
/--
info: The following set of actions must preserve the invariant, satisfy the step properties, and successfully terminate:
  freeze
    frozen_stays_r ... ✅
    doesNotThrow ... ✅
    frozen_mono ... ✅
    frozen_r ... ✅
-/
#guard_msgs in
#check_action StepRegMod freeze

-- `#prove_action` persists every cell (step cells included) and emits the
-- preservation lemma; its summary lines carry timings, so they are not pinned.
namespace StepRegMod.Proofs
#prove_action StepRegMod initializer
#prove_action StepRegMod mark
#prove_action StepRegMod reset
#prove_action StepRegMod freeze
end StepRegMod.Proofs

namespace StepRegMod
#gen_composition StepRegMod
end StepRegMod

/-- info: 'StepRegMod.Proofs.freeze_frozen_stays_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepRegMod.Proofs.freeze_frozen_stays_r

/-- info: 'StepRegMod.frozen_mono_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepRegMod.frozen_mono_step

/-- info: 'StepRegMod.frozen_stays_r_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepRegMod.frozen_stays_r_step

/-- info: 'StepRegMod.reachable_frozen_stays_r_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepRegMod.reachable_frozen_stays_r_step

/-- info: #veil_status StepRegMod: 14/14 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status StepRegMod
