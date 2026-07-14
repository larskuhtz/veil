import VeilTest.GenCompositionBase

/-! # `#gen_composition` test — the proof/certificate consumer

The consumer half of the M6 file-family test: cross-file `#prove_action`
for every action (which persists each cell as a kernel-checked theorem
*and* emits the per-action preservation lemma `step_<action>` /
`init_case`), then `#gen_composition` assembling them into
`CompRing.invariants_of_reachable` + named `reachable_<property>`
projections. The `#guard_msgs` pins are the acceptance check: the composed
certificate is a real proof over the standard axioms, no `sorryAx`
anywhere. -/

set_option linter.unusedVariables false

open Veil CompRing

set_option veil.smt.trust false

namespace CompRing.Proofs
#prove_action CompRing initializer
#prove_action CompRing elect
#prove_action CompRing abstain
end CompRing.Proofs

namespace CompRing
#gen_composition CompRing
end CompRing

/-- info: 'CompRing.Proofs.init_case' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.Proofs.init_case

/-- info: 'CompRing.Proofs.step_abstain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.Proofs.step_abstain

/-- info: 'CompRing.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.invariants_of_reachable

/-- info: 'CompRing.reachable_leader_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.reachable_leader_unique
