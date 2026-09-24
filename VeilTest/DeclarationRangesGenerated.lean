import VeilTest.DeclarationRanges

/-! # Source locations of step lemmas, VC theorems and composition exports

Continues `VeilTest/DeclarationRanges.lean` (whose `#decl_ranges` this
uses) for the declarations of the port branches: the step lemmas derived at
`#gen_spec` point at the action or state component they are about; the VC
theorems, preservation lemmas and composition exports — about several user
declarations, and possibly emitted in another file — point at the command
that emitted them. -/

set_option linter.unusedVariables false

veil module RangeGenMod

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

action freeze (n : node) {
  require r n
  frozen n := true
}

invariant [frozen_r] frozen N → r N

step_property [frozen_mono] { frozen N → frozen' N }

#gen_spec

#gen_theorems

#gen_composition RangeGenMod

end RangeGenMod

/-! ## Step lemmas point at their action or state component -/

/--
info: RangeGenMod.frozen_mono: line 40, selects `frozen_mono`
---
info: RangeGenMod.mark.frame_frozen: line 28, selects `mark`
---
info: RangeGenMod.mark.mono_r: line 28, selects `mark`
---
info: RangeGenMod.freeze.tr_of_step: line 33, selects `freeze`
---
info: RangeGenMod.r.mono: line 18, selects `r`
---
info: RangeGenMod.r.init: line 18, selects `r`
-/
#guard_msgs in
#decl_ranges RangeGenMod.frozen_mono RangeGenMod.mark.frame_frozen RangeGenMod.mark.mono_r
  RangeGenMod.freeze.tr_of_step RangeGenMod.r.mono RangeGenMod.r.init

/-! ## Emitted declarations point at the emitting command -/

/--
info: RangeGenMod.mark_frozen_r: line 44, selects `#gen_theorems`
---
info: RangeGenMod.freeze_frozen_mono: line 44, selects `#gen_theorems`
---
info: RangeGenMod.step_mark: line 44, selects `#gen_theorems`
---
info: RangeGenMod.frozen_mono_step: line 44, selects `#gen_theorems`
---
info: RangeGenMod.invariants_of_reachable: line 46, selects `#gen_composition`
---
info: RangeGenMod.reachable_frozen_r: line 46, selects `#gen_composition`
-/
#guard_msgs in
#decl_ranges RangeGenMod.mark_frozen_r RangeGenMod.freeze_frozen_mono RangeGenMod.step_mark
  RangeGenMod.frozen_mono_step RangeGenMod.invariants_of_reachable RangeGenMod.reachable_frozen_r
