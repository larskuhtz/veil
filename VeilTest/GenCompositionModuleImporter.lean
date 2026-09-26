import VeilTest.GenCompositionModule

/-! # `#gen_composition` test — importer of a `module` consumer

The per-action lemmas and the composed certificate persisted by the
`module` file `GenCompositionModule.lean` are visible here, with their
proofs (the axiom pins see through to the real proof terms). -/

open Veil CompRing

/-- info: 'CompRing.Proofs.step_abstain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.Proofs.step_abstain

/-- info: 'CompRing.invariants_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.invariants_of_reachable

/-- info: 'CompRing.reachable_leader_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompRing.reachable_leader_unique

/-- info: #veil_status CompRing: 9/9 real; axioms: propext, Classical.choice, Quot.sound -/
#guard_msgs in
#veil_status CompRing
