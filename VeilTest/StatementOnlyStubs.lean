import Veil

/-! # Solve-free statement-only stubs (`veil.gen.statementOnlyTheorems`)

Under `veil.gen.statementOnlyTheorems`, `#gen_theorems` persists statement
stubs WITHOUT starting or awaiting any invariant discharger: this file runs
no check command, yet `#gen_theorems` must persist a `sorryAx` stub for every
generated induction VC — including both the WP and TR encodings of each cell
(there is no "which form proved" fact in solve-free mode) — and each stub's
axiom closure contains `sorryAx` (plus the classical axioms its statement's
definitions pull in): a stub carries no verification claim.
(`#gen_spec` still starts its `doesNotThrow` probe asynchronously, so the
summary's incidental proven-count is racy — the axiom pins below are the
deterministic part of this test.)

The model is `Ring.lean`'s leader-election ring, renamed so declarations
cannot collide with the other test modules. -/

set_option linter.unusedVariables false
set_option veil.gen.statementOnlyTheorems true

veil module StubRing

type node

instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node -> Bool
relation pending : node -> node -> Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

action send (n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  pending n next := true
}

action recv (sender n next : node) {
  require ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)
  require pending sender n
  pending sender n := false
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
invariant [leader_greatest] leader L → le N L
invariant [inv_1] pending S D ∧ btw S N D → le N S
invariant [inv_2] pending L L → le N L

#gen_spec

-- No check command: the stub pass below must not trigger one. The summary's
-- proven-count clause depends on how far the async `doesNotThrow` probe got,
-- so the info message is dropped rather than pinned.
#guard_msgs (drop info) in
#gen_theorems

end StubRing

-- Every stub — the WP form, the TR alternative, and `doesNotThrow` — exists
-- and has `sorryAx` in its axiom closure: statements persisted, nothing
-- claimed. (The extra classical axioms come from the WP statements'
-- definitions; the TR encoding's statement happens not to pull any in.)
/-- info: 'StubRing.recv_single_leader' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StubRing.recv_single_leader

/-- info: 'StubRing.recv_single_leader_tr' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms StubRing.recv_single_leader_tr

/-- info: 'StubRing.send_doesNotThrow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StubRing.send_doesNotThrow
