import Veil

/-! # `step_property` — two-state properties as checked cells

A `step_property` relates a pre-state and a post-state (post-state components
primed, as in `transition` bodies). It is checked once per action under the
module's assumptions and invariants at the pre-state, sits in the VC grid and
the registry like an invariant cell, is persisted by `#gen_theorems`, and is
exported over every label as `<property>_step`. The four properties below
cover the class: one the update records alone would give (a relation only
ever set), one that needs the actions' guards (frozen entries are stable),
one that needs an invariant at the pre-state, and one over a `Nat`. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.gen.vcRegistry true

veil module StepPropMod

type node

relation r : node → Bool
relation q : node → node → Bool
relation frozen : node → Bool
individual c : Nat

#gen_state

after_init {
  r N := false
  q N M := false
  frozen N := false
  c := 0
}

action mark (n : node) {
  require ¬ frozen n
  r n := true
}

action reset (n : node) {
  require ¬ frozen n
  r n := false
}

action link (n m : node) {
  require r n
  q n m := true
}

action freeze (n : node) {
  require r n
  frozen n := true
}

action tick {
  c := c + 1
}

invariant [frozen_r] frozen N → r N

-- Derivable from the update records alone (the generated `frozen.mono`
-- states the same fact); here it is a *checked* cell.
step_property [frozen_mono] { frozen N → frozen' N }
-- Needs the guards: `mark` and `reset` require `¬ frozen n`.
step_property [r_stable_when_frozen] { frozen N → r' N = r N }
-- Needs the invariant at the pre-state (`frozen_r`) and the guards.
step_property [frozen_stays_r] { frozen N → r' N }
-- A non-`Bool` component.
step_property [c_monotone] { c ≤ c' }

#gen_spec

-- The step cells sit under their action next to the invariant cells; the
-- header says so.
/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  frozen_r ... ✅
The following set of actions must preserve the invariant, satisfy the step properties, and successfully terminate:
  reset
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    r_stable_when_frozen ... ✅
    frozen_stays_r ... ✅
    c_monotone ... ✅
  mark
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    r_stable_when_frozen ... ✅
    frozen_stays_r ... ✅
    c_monotone ... ✅
  freeze
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    r_stable_when_frozen ... ✅
    frozen_stays_r ... ✅
    c_monotone ... ✅
  tick
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    r_stable_when_frozen ... ✅
    frozen_stays_r ... ✅
    c_monotone ... ✅
  link
    doesNotThrow ... ✅
    frozen_r ... ✅
    frozen_mono ... ✅
    r_stable_when_frozen ... ✅
    frozen_stays_r ... ✅
    c_monotone ... ✅
-/
#guard_msgs in
#check_invariants

-- Persists every cell (step cells included) and emits the preservation
-- lemmas plus one `<property>_step` per step property; the summary lines
-- carry timings, so they are not pinned.
#gen_theorems

-- In the module's namespace: adds `reachable_<property>_step` on top.
#gen_composition StepPropMod

end StepPropMod

/-! ## Persisted cells and the whole-system export -/

/-- info: 'StepPropMod.reset_r_stable_when_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepPropMod.reset_r_stable_when_frozen

/-- info: 'StepPropMod.freeze_frozen_stays_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepPropMod.freeze_frozen_stays_r

/-- info: 'StepPropMod.frozen_mono_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepPropMod.frozen_mono_step

/-- info: 'StepPropMod.frozen_stays_r_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepPropMod.frozen_stays_r_step

/-- info: 'StepPropMod.c_monotone_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepPropMod.c_monotone_step

/-- info: 'StepPropMod.reachable_frozen_stays_r_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepPropMod.reachable_frozen_stays_r_step

/-- info: #veil_status StepPropMod: 32/32 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status StepPropMod

-- The exported statements, as a downstream consumer sees them: sort
-- binders implicit, `Inhabited` explicit, `Invariants` at the module's
-- canonical instantiation.
#check @StepPropMod.frozen_stays_r_step
#check @StepPropMod.reachable_frozen_stays_r_step

section
variable {node : Type} [Inhabited node]

-- The reachable form is consumed directly: any step from a reachable state
-- satisfies the property, `StepPropMod.frozen_stays_r th s s'` at the
-- module's canonical instantiation (the `#check` above shows the statement;
-- the instantiation's representation instances are explicit arguments there,
-- so the conclusion is left to inference here).
example {th : StepPropMod.Theory node}
    {s s' : StepPropMod.State (StepPropMod.FieldAbstractType node)} {l : StepPropMod.Label node}
    (hr : (StepPropMod.relationalTransitionSystem node).reachable th s)
    (h : (StepPropMod.relationalTransitionSystem node).tr th s l s') :=
  StepPropMod.reachable_frozen_stays_r_step hr h

end

/-! ## A step property that fails on one action -/

veil module StepPropFail

type node

relation r : node → Bool
relation frozen : node → Bool

#gen_state

after_init {
  r N := false
  frozen N := false
}

action mark (n : node) {
  r n := true
}

action reset (n : node) {
  require ¬ frozen n
  r n := false
}

invariant true

-- `reset` falsifies it: the cell is refuted (the counterexample model is
-- not pinned, so its printing is off).
step_property [r_mono] { r N → r' N }

#gen_spec

/--
error: Initialization must establish the invariant:
  doesNotThrow ... ✅
  inv_0 ... ✅
The following set of actions must preserve the invariant, satisfy the step properties, and successfully terminate:
  reset
    doesNotThrow ... ✅
    inv_0 ... ✅
    r_mono ... ❌
  mark
    doesNotThrow ... ✅
    inv_0 ... ✅
    r_mono ... ✅
-/
#guard_msgs in
set_option veil.printCounterexamples false in
#check_invariants

end StepPropFail

/-! ## Only mutable components have a post-state -/

veil module StepPropImmutable

type node

immutable individual k : Nat
individual c : Nat

#gen_state

after_init {
  c := 0
}

action tick {
  c := c + k
}

invariant true

/--
error: `k'`: `k` is an immutable state component, so it has no post-state value. Write `k`; only mutable components have a primed form in a `step_property`.
-/
#guard_msgs in
step_property [bad] { k' = k }

#gen_spec

end StepPropImmutable
