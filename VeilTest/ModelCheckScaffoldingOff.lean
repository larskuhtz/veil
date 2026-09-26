import Veil

/-! # Codegen gating: `veil.gen.modelCheckScaffolding false`

With the option off, `#gen_spec` skips the `Label` enumeration scaffolding
(`Enumeration` / `FinEncodableInjOnly` on `Label`, the `ActionTag` enum and
the `EnumerableTransitionSystem`) — the derivation that stops scaling on
modules with many parameterised actions. Verification is unaffected;
`#model_check` and `#simulate` fail with a clear message instead of a
missing-instance error. -/

veil module ScaffoldOff

type node
relation flag (n : node)

#gen_state

after_init {
  flag N := false
}

action raise (n : node) {
  flag n := true
}

invariant [flag_ok] True

set_option veil.gen.modelCheckScaffolding false
#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  flag_ok ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  raise
    doesNotThrow ... ✅
    flag_ok ... ✅
-/
#guard_msgs in
#check_invariants

/--
error: `#model_check` and `#simulate` require `veil.gen.modelCheckScaffolding` (currently false). Re-enable it to generate the EnumerableTransitionSystem. `#check_invariants` and `#check_action` do not require it.
-/
#guard_msgs in
#model_check interpreted { node := Fin 2 } {}

/--
error: `#model_check` and `#simulate` require `veil.gen.modelCheckScaffolding` (currently false). Re-enable it to generate the EnumerableTransitionSystem. `#check_invariants` and `#check_action` do not require it.
-/
#guard_msgs in
#simulate interpreted { node := Fin 2 } {} (seed := 1)

end ScaffoldOff
