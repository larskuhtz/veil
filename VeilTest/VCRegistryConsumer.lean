import VeilTest.VCRegistryBase

/-! # VC registry test — the cross-file consumer

Exercises the cross-file commands against `VCRegistryBase.lean`'s persisted
VC registry: a single-cell check, and per-action proof persistence with
kernel-checked reconstruction (the statements are the persisted `Expr`s, so
what is proven here is what the base module's sweep checks, by
construction). -/

set_option linter.unusedVariables false

open Veil RegRing

-- Cross-file per-action proof persistence, with proof reconstruction: the
-- persisted theorems must carry no `sorryAx`. The option is read at tactic
-- runtime on the cross-file path (no `#gen_spec` capture applies).
set_option veil.smt.trust false

namespace RegRing.Slice
-- Manual-cell override first: `#prove_action` below must consume this
-- theorem as-is (after a statement check) instead of re-solving the cell.
#prove_vc RegRing recv single_leader by veil_solve_wp
#prove_action RegRing recv
end RegRing.Slice

/-- info: 'RegRing.Slice.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RegRing.Slice.recv_single_leader

/-- info: 'RegRing.Slice.recv_doesNotThrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RegRing.Slice.recv_doesNotThrow
