import Veil

/-! # Bool-atom fold (`veil.smt.foldBoolAtoms`)

`__veil_fold_bool_atoms` replaces `f a⃗ = true` atoms over local Bool-valued
function variables by applications of opaque Prop-valued local definitions
before the SMT query is built, so lean-smt's whole-telescope `embedding`
pass short-circuits (its congruence proof is the dominant component of
every reconstruction witness).

The module shape deliberately mirrors `VCRegistryBase.lean`'s ring
(`require`s, if-then-else over Bool relations, an action with extracted
`Decidable` parameters) — the fold must be green on all of it in
reconstruction mode. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.gen.vcRegistry true

veil module FoldRing

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

#check_invariants

end FoldRing

/-! ## Fold effectiveness and trust base

A cell proved through the fold must carry the standard three axioms, and
its witness must contain no whole-telescope preprocessing segment: the
material between the `Classical.byContradiction` node (lean-smt's
`negateGoal`) and the `implies_false_of_not_and` reconstruction glue is
the preprocessing `Eq.mpr` congruence proof, which the fold is designed
to eliminate (measured 6–14 K objects per cell without it — a handful of
structural nodes with it). -/

open Veil FoldRing

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
-- fresh solve, so the witness below reflects the fold (a cache hit would
-- replay whatever an earlier build stored)
set_option veil.cache.proofs false

#prove_vc FoldRing recv single_leader by veil_solve_wp

/-- info: 'recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms recv_single_leader

open Lean in
private def subDagObjsAt (pf : Expr) (c : Name) : IO Nat := do
  match pf.find? (fun e => e.isApp && (e.getAppFn.constName? == some c)) with
  | some e => e.numObjs
  | none => pure 0

open Lean in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let some info := (← getEnv).find? `recv_single_leader | throwError "cell missing"
  let some v := info.value? | throwError "no proof value"
  let smtN ← subDagObjsAt v ``Classical.byContradiction
  let glueN ← subDagObjsAt v `Smt.Reconstruct.Prop.implies_false_of_not_and
  unless smtN > 0 && glueN > 0 do
    throwError "witness shape changed: expected byContradiction + reconstruction glue"
  let pre := smtN - glueN
  unless pre < 1000 do
    throwError "fold ineffective: preprocessing segment is {pre} objects (expected < 1000; \
      ~9000 without the fold at this module's scale)"
  IO.println s!"fold effective: preprocessing segment = {pre} objects"
