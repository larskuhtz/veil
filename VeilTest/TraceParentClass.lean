import Veil

/-! # Trace queries on a module instantiating a class with an `extends` parent

The trace (BMC) path destructures instantiated classes through the
`rcases`-pattern destructuring (`veil_destruct`). For a class with an
`extends` parent, the parent is an instance-implicit constructor field, and a
plain anonymous-constructor pattern distributes the field names over the
explicit fields only — every name shifted by one and the last field handed a
nested tuple, which failed the trace with "`<field> : … is not an inductive
datatype`" while the sweep (whose fast path iterates `cases_type*`) passed.
The pattern is now explicit (`@⟨…⟩`). A controlled pair: the module with the
parent and its twin with the parent's fields inlined must both sweep and
trace green. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false

class TSS (state : Type) where
  init : state → Prop
  step : state → state → Prop
  trans : state → state → Prop
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'

class WithParent (validator state : Type) (byz : validator → Prop)
    extends TSS state where
  propose : state → validator → state → Prop
  propose_trans : ∀ st p st', propose st p st' → trans st st'
  proposed : state → validator → Prop
  has_decided : state → validator → Prop
  proposed_mono : ∀ st st' p, trans st st' → proposed st p → proposed st' p
  integrity : ∀ st, reachable st → ∀ i, ¬ byz i → has_decided st i → proposed st i

/-- The control: the same fields, the parent inlined. -/
class Flat (validator state : Type) (byz : validator → Prop) where
  init : state → Prop
  step : state → state → Prop
  trans : state → state → Prop
  reachable : state → Prop
  step_trans : ∀ st st', step st st' → trans st st'
  reachable_init : ∀ st, init st → reachable st
  reachable_trans : ∀ st st', reachable st → trans st st' → reachable st'
  propose : state → validator → state → Prop
  propose_trans : ∀ st p st', propose st p st' → trans st st'
  proposed : state → validator → Prop
  has_decided : state → validator → Prop
  proposed_mono : ∀ st st' p, trans st st' → proposed st p → proposed st' p
  integrity : ∀ st, reachable st → ∀ i, ¬ byz i → has_decided st i → proposed st i

class FM (validator : Type) where
  byz : validator → Prop

veil module TraceParent

type node
type astate
instantiate fm : FM node
instantiate a : WithParent node astate fm.byz
immutable individual a0 : astate
individual ast : astate
relation touched (i : node)

#gen_state

assumption [a0_init] a.init a0

after_init {
  ast := a0
  touched I := false
}

action a_step (a_next : astate) {
  require a.trans ast a_next
  ast := a_next
}

action touch (i : node) {
  require ¬ fm.byz i
  require a.has_decided ast i
  touched i := true
}

invariant [a_reach] a.reachable ast
invariant [touched_proposed] ∀ i, ¬ fm.byz i → touched i → a.proposed ast i

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  a_reach ... ✅
  touched_proposed ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  a_step
    doesNotThrow ... ✅
    a_reach ... ✅
    touched_proposed ... ✅
  touch
    doesNotThrow ... ✅
    a_reach ... ✅
    touched_proposed ... ✅
-/
#guard_msgs in
#check_invariants

-- The witness is dropped (it prints the model); a failing trace is an error.
#guard_msgs (drop info) in
sat trace {
  a_step
  assert (a.reachable ast)
}

end TraceParent

veil module TraceFlat

type node
type astate
instantiate fm : FM node
instantiate a : Flat node astate fm.byz
immutable individual a0 : astate
individual ast : astate
relation touched (i : node)

#gen_state

assumption [a0_init] a.init a0

after_init {
  ast := a0
  touched I := false
}

action a_step (a_next : astate) {
  require a.trans ast a_next
  ast := a_next
}

action touch (i : node) {
  require ¬ fm.byz i
  require a.has_decided ast i
  touched i := true
}

invariant [a_reach] a.reachable ast
invariant [touched_proposed] ∀ i, ¬ fm.byz i → touched i → a.proposed ast i

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  a_reach ... ✅
  touched_proposed ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  a_step
    doesNotThrow ... ✅
    a_reach ... ✅
    touched_proposed ... ✅
  touch
    doesNotThrow ... ✅
    a_reach ... ✅
    touched_proposed ... ✅
-/
#guard_msgs in
#check_invariants

-- The witness is dropped (it prints the model); a failing trace is an error.
#guard_msgs (drop info) in
sat trace {
  a_step
  assert (a.reachable ast)
}

end TraceFlat
