import Veil

/-! # `trSimp`: the pre-computed transitions as one simp set

Two-state facts about a generated action (a frame, a monotonicity fact)
are proven from the action's pre-computed transition `<action>.ext.tr`,
reached from the derived transition by `<action>.ext.derived_eq`. The
`actSimp`/`nextSimp` sets unfold the action *bodies* first and defeat that
rewrite, so consumers kept hand-maintained per-action lemma lists. The
`trSimp` set holds exactly the `derived_eq` theorems and the `tr`
definitions: after `cases` on the label,
`simp only [M.relationalTransitionSystem, M.Next, M.NextAct] at h; simp only [trSimp] at h`
exposes the transition body — guards and the `setIn {…} s₀ = s₁`
equation — for every action, and one uniform script closes each case.
(`obtain ⟨_, h⟩ := h` on the final equation substitutes the post-state, so
no `subst` follows.) -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

veil module TrSimpMod

type node

relation marked : node → Bool
individual count : Nat

#gen_state

after_init {
  marked N := false
  count := 0
}

action mark (n : node) {
  require ¬ marked n
  marked n := true
}

action tick {
  count := count + 1
}

action reset {
  count := 0
}

invariant [nonneg] count ≥ 0

#gen_spec

end TrSimpMod

open Veil TrSimpMod

section
variable {node : Type} [Inhabited node] [DecidableEq node]
  {th : TrSimpMod.Theory node}
  {st st' : TrSimpMod.State (TrSimpMod.FieldAbstractType node)}

/-- Evaluate the field-representation `get`/`set` pair at the canonical
(functional) representation. -/
local macro "field_simp_all" : tactic =>
  `(tactic| simp_all [Veil.FieldRepresentation.set, Veil.FieldRepresentation.get,
      Veil.CanonicalField.set, Veil.FieldUpdateDescr.fieldUpdate, Veil.FieldUpdatePat.match,
      Veil.IteratedArrow.curry, Veil.IteratedArrow.uncurry, Veil.IteratedProd.patCmp,
      instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id])

/-- `marked` is only ever set: a monotonicity fact over every label, with one
uniform script — the transition body of each action is exposed by `trSimp`. -/
theorem marked_mono (l : TrSimpMod.Label node)
    (h : (TrSimpMod.relationalTransitionSystem node).tr th st l st') (n : node)
    (hm : st.marked n = true) : st'.marked n = true := by
  cases l <;> simp only [TrSimpMod.relationalTransitionSystem, TrSimpMod.Next, TrSimpMod.NextAct] at h
    <;> simp only [trSimp] at h
  all_goals
    (repeat (obtain ⟨_, h⟩ := h))
    field_simp_all

/-- `mark` leaves `count` unchanged: a frame fact for one action. -/
theorem mark_frame_count (n : node)
    (h : (TrSimpMod.relationalTransitionSystem node).tr th st (TrSimpMod.Label.mark n) st') :
    st'.count = st.count := by
  simp only [TrSimpMod.relationalTransitionSystem, TrSimpMod.Next, TrSimpMod.NextAct] at h
  simp only [trSimp] at h
  obtain ⟨_, h⟩ := h
  subst h
  field_simp_all

/-- Guard: `trSimp` holds only the `derived_eq` theorems and the `tr`
definitions — the action bodies are not unfolded, so the exposed body is
the pre-computed one and the `derived_eq` rewrite is not defeated. The
`mark` body after the two simps is the guard and the `setIn` equation. -/
example (n : node)
    (h : (TrSimpMod.relationalTransitionSystem node).tr th st (TrSimpMod.Label.mark n) st') :
    True := by
  simp only [TrSimpMod.relationalTransitionSystem, TrSimpMod.Next, TrSimpMod.NextAct] at h
  simp only [trSimp] at h
  obtain ⟨hguard, heq⟩ := h
  guard_hyp hguard : _ ≠ true
  guard_hyp heq : _ = st'
  trivial

end
