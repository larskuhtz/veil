import Veil

/-! # `Inhabited (State (FieldAbstractType …))` from the sort instances alone

The generated `instInhabitedStateFieldConcreteType` takes one
`[Inhabited (χ f)]` argument per field; from a plain section outside the
module, `#synth Inhabited (M.State (M.FieldAbstractType …))` used to fail
with only the sort instances in scope, and consumers of the generated
transition system (whose `default` is the initializer's pre-state) wrote
the instance by hand. `#gen_state` now also emits
`instInhabitedStateFieldAbstractType`, over the sorts' `Inhabited`
binders alone. -/

set_option linter.unusedVariables false

veil module InhabitedAbstract

type node
type slot

individual leader : node
relation voted : node → slot → Bool
function chosen : slot → node

#gen_state

after_init {
  leader := leader
  voted N S := false
  chosen S := chosen S
}

action vote (n : node) (s : slot) {
  voted n s := true
}

invariant [trivially] voted N S → voted N S

#gen_spec

end InhabitedAbstract

section
-- A fresh section with nothing but the sort instances.
variable {node slot : Type} [Inhabited node] [Inhabited slot]

/-- info: InhabitedAbstract.instInhabitedStateFieldAbstractType node slot -/
#guard_msgs in
#synth Inhabited (InhabitedAbstract.State (InhabitedAbstract.FieldAbstractType node slot))

example : InhabitedAbstract.State (InhabitedAbstract.FieldAbstractType node slot) := default

end
