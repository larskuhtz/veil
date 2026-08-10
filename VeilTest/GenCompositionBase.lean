import Veil

/-! # `#gen_composition` test — the defining module

The model half of the file-family test: a
registry-only model — `#gen_spec` persists the VC registry, **no in-file
sweep, no theorem persistence** — whose proofs live entirely in the
consumer (`VeilTest/GenComposition.lean`), exactly like the verified-module
file family's model files. (`transition`-syntax actions are deliberately
absent: they have no `derived_eq`, and the preservation-lemma emission
rejects their TR-form cells with a dedicated error — see `cellLeaf` in
`Veil/Frontend/DSL/Module/Composition.lean`.) -/

set_option linter.unusedVariables false
set_option veil.gen.vcRegistry true

veil module CompRing

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

end CompRing
