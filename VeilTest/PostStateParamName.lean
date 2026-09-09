import Veil

/-! # Action parameters named like the generated transition binders

The generated transition relations bind a reader, a pre-state, a label and
a post-state; the `transition` syntax binds a theory, a pre- and a
post-state. Those binders are implementation details and must not capture
an action parameter of the same name: an action parameter called `st'`
used to pass the sweep and fail every `sat trace` with an application type
mismatch naming `<action>.ext.tr … st' rd st st'`. Here every such name is
an action or transition parameter, and the sweep and a trace both pass. -/

set_option linter.unusedVariables false

veil module PostStateParamName

type node

relation marked : node → Bool
relation seen : node → Bool

#gen_state

after_init {
  marked N := false
  seen N := false
}

-- Action parameters named like the `Next`/`Next'` binders.
action mark (st' : node) (st : node) (rd : node) (label : node) {
  marked st' := true
  seen st := true
  seen rd := true
  seen label := true
}

-- `transition` parameters named like the theory/state template binders.
transition unmark (st' : node) (th : node) (st : node) {
  (∀ n, (marked' n ↔ (marked n ∧ n ≠ st'))) ∧
  (∀ n, (seen' n ↔ (seen n ∨ n = th ∨ n = st)))
}

invariant [trivially] marked N → marked N

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  trivially ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  unmark
    doesNotThrow ... ✅
    trivially ... ✅
  mark
    doesNotThrow ... ✅
    trivially ... ✅
-/
#guard_msgs in
#check_invariants

-- The trace must be found (an error here is the capture: without the fix the
-- action's `st'` was captured by the `Next'` binder and every trace failed
-- with an application type mismatch). Its model dump is solver-dependent, so
-- only the absence of errors is asserted. (The `transition` is exercised by
-- the sweep above; the trace encoding of a `transition` with equalities on a
-- sort is a separate limitation.)
#guard_msgs (drop info) in
sat trace {
  mark
  assert (∃ n, seen n)
}

end PostStateParamName
