import VeilTest.DefinitionSites

/-! # Definition site of a `step_property`

Continues `VeilTest/DefinitionSites.lean` (whose `#def_sites` this uses):
a named step property's name is its definition site too. -/

set_option linter.unusedVariables false

veil module StepSiteMod

type node

relation frozen : node → Bool

#gen_state

after_init {
  frozen N := false
}

action freeze (n : node) {
  frozen n := true
}

/-- info: `frozen_mono` (line 29) defines StepSiteMod.frozen_mono -/
#guard_msgs in
#def_sites in
step_property [frozen_mono] { frozen N → frozen' N }

#gen_spec

end StepSiteMod
