import Veil

/-! # VC registry test — the defining module

`veil.gen.vcRegistry` makes `#gen_spec` persist the module's VC registry
(statements pre-elaborated to `Expr`s) into the olean, so that
`VeilTest/VCRegistryConsumer.lean` can check and prove this module's VCs
cross-file. The model is `Ring.lean`'s leader-election ring, renamed so the
two files' declarations cannot collide. -/

set_option linter.unusedVariables false
set_option veil.gen.vcRegistry true

veil module RegRing

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

-- The in-file sweep must coexist with registry persistence.
#check_invariants

end RegRing
