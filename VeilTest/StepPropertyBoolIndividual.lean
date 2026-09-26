import Veil

/-! # `step_property` with a zero-arity `Bool` component

Regression test. On the transition (TR) route, field concretization unfolds
`CanonicalField doms cod` in each concretized field's own type, but a frame
equality `st'.flag = st.flag` of a zero-arity field kept it as the implicit
type of its `Eq`: `@Eq (CanonicalField [] Bool) st'.flag st.flag`. lean-smt's
Bool embedding matches `Bool` syntactically, so the equation reached the
translation as `decide x = decide y` over `Classical.propDecidable`, and every
step cell of such a module failed with the solver crash
`Expected SMT-LIBv2 sort constructor, got '('` — whatever the step property
says, since the frame of `flag` is a hypothesis of every action's cell. A
`node`-typed individual in place of `flag` did not trigger it. -/

set_option veil.smt.trust false

veil module StepPropBoolIndividual

type node
individual flag : Bool
individual count : Nat
relation seen : node → Bool

#gen_state

after_init {
  flag := false
  count := 0
  seen N := false
}

action bump {
  count := count + 1
}

action see (n : node) {
  seen n := true
}

invariant [trivial] True

step_property [seen_mono] { seen N → seen' N }

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  trivial ... ✅
The following set of actions must preserve the invariant, satisfy the step properties, and successfully terminate:
  see
    doesNotThrow ... ✅
    trivial ... ✅
    seen_mono ... ✅
  bump
    doesNotThrow ... ✅
    trivial ... ✅
    seen_mono ... ✅
-/
#guard_msgs in
#check_invariants

end StepPropBoolIndividual
