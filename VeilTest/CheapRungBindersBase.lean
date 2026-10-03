module

public import Veil

/-! # Cheap rung, goals with introduced binders — the model

`VeilTest/CheapRungBinders.lean` checks `veil_solve_frame` on the two goal
shapes Veil's simplification hands it for a *frame* cell, and on a cell
it must decline. After `unveil_local` the projected conjunct is always the
quantified invariant, `∀ M N, pair M N = true → pair N M = true`; the goal
is one of

* **quantified** — the binders are still in the goal, behind the action's
  guards (`link`, which has guards);
* **introduced** — the binders are already local variables and only the
  hypotheses remain in the goal, `pair M N = true → pair N M = true`
  (`raise_flag`, which has no guard).

`tag_closed` has two hypotheses over two binders, so in its introduced
shape no single binder group can be instantiated by unifying the
conclusion alone: `I` is fixed by `tag I`, `J` only by a hypothesis. -/

set_option linter.unusedVariables false
set_option veil.gen.vcRegistry true
set_option veil.smt.trust false

veil module CheapRungBindersModel

type node

relation flag : node -> Bool
relation tag : node -> Bool
relation mark : node -> node -> Bool
relation pair : node -> node -> Bool

#gen_state

after_init {
  flag N := false
  tag N := false
  mark M N := false
  pair M N := false
}

/-- No guard: the frame cells of this action reach the rung in the
introduced shape. -/
action raise_flag (n : node) {
  flag n := true
}

/-- Guarded: the frame cells of this action reach the rung in the
quantified shape. -/
action link (m n : node) {
  require flag m
  require tag n → tag m
  mark m n := true
}

invariant [mark_needs_flag] mark M N → flag M
invariant [tag_closed] tag J → mark I J → tag I
invariant [pair_sym] pair M N → pair N M

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  mark_needs_flag ... ✅
  tag_closed ... ✅
  pair_sym ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  raise_flag
    doesNotThrow ... ✅
    mark_needs_flag ... ✅
    tag_closed ... ✅
    pair_sym ... ✅
  link
    doesNotThrow ... ✅
    mark_needs_flag ... ✅
    tag_closed ... ✅
    pair_sym ... ✅
-/
#guard_msgs in
#check_invariants

end CheapRungBindersModel
