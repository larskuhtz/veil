import Veil

/-! # `#gen_composition` on a `#gen_theorems` module

The in-file counterpart of `GenComposition.lean`: the module is verified
and its cells persisted *inside* the defining module (`#check_invariants`
+ `#gen_theorems`), and `#gen_theorems` then emits the same per-action
preservation lemmas (`init_case` / `step_<action>`) that `#prove_action`
emits per proof file — so `#gen_composition` in the module's namespace
assembles `invariants_of_reachable` + the named `reachable_<property>`
projections without any hand-written induction. Proof reconstruction is
on, so the axiom pins are the acceptance check: real proofs over the
standard axioms, no `sorryAx`. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false

veil module GTRing

type node

instantiate tot : TotalOrder node
open TotalOrder

relation leader : node -> Bool
relation voted : node -> Bool

#gen_state

after_init {
  leader N := false
  voted N := false
}

action elect (n : node) {
  require ∀ N, le N n
  leader n := true
}

action abstain (n : node) {
  voted n := true
}

safety [leader_greatest] leader L → le N L
invariant [leader_unique] leader N ∧ leader M → N = M

#gen_spec

#check_invariants

#gen_theorems

-- Idempotent: a second `#gen_theorems` finds every lemma already present.
#gen_theorems

-- In the module's namespace, as the composition of a `#gen_theorems`
-- module is meant to be invoked.
#gen_composition GTRing

end GTRing

/-- info: 'GTRing.init_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GTRing.init_case

/-- info: 'GTRing.step_elect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GTRing.step_elect

/-- info: 'GTRing.step_abstain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GTRing.step_abstain

/-- info: 'GTRing.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GTRing.invariants_of_reachable

/-- info: 'GTRing.reachable_leader_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GTRing.reachable_leader_unique

-- The composed statements, as a downstream consumer sees them: the sort
-- binders implicit, the instances explicit, `th`/`st` inferred from the
-- reachability hypothesis.
#check @GTRing.invariants_of_reachable
#check @GTRing.reachable_leader_unique

-- The post-`end` form (a certificate file re-opening the namespace) is
-- idempotent on top of the in-module one.
namespace GTRing
#gen_composition GTRing
end GTRing
