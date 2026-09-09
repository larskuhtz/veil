import Veil

/-! # An `assumption` naming a mutable component says why it is rejected

An `assumption` is a background axiom over the immutable part of the state.
One that names a mutable component used to fail, correctly but opaquely,
with "Unbound uncapitalized variable: `os`" from the theory-only
elaboration. It is now rejected at the identifier with a message that says
what an `assumption` may range over and what to use instead. -/

set_option linter.unusedVariables false

veil module AssumptionMutable

type ostate

immutable individual os0 : ostate
individual os : ostate
relation done : Bool

#gen_state

/--
error: `os` is a mutable state component, but an `assumption` is a background axiom: it ranges over the immutable part of the state only (`immutable` components, sorts and instantiated classes). State a property of the mutable state as an `invariant` (checked) or a `trusted invariant` (assumed).
-/
#guard_msgs in
assumption [os_is_initial] os = os0

-- The immutable component is fine.
assumption [os0_fixed] os0 = os0

after_init {
  os := os0
  done := false
}

action finish {
  done := true
}

invariant [os_fixed] os = os0

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  os_fixed ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  finish
    doesNotThrow ... ✅
    os_fixed ... ✅
-/
#guard_msgs in
#check_invariants

end AssumptionMutable
