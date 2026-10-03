import VeilTest.CheapRungBindersBase

/-! # Cheap rung, goals with introduced binders

`veil_solve_frame` closes a frame cell by projecting the invariant's
conjunct `h` from the pre-state clump. It has two matchers: `exact h` /
`exact h ..` between `intro`s, and, on its misses, a telescope matcher
that instantiates *all* of `h`'s binders with metavariables, unifies the
conclusion and fills each hypothesis from the context. This file pins, on
the model of `VeilTest/CheapRungBindersBase.lean`:

* the introduced goal shape is real, and the first matcher misses it;
* the rung closes frame cells in both shapes, with the standard axioms;
* cells that are not frames still decline, so the ladder's SMT rung
  proves them. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false

open Veil CheapRungBindersModel

/-! ## The introduced shape defeats the first matcher

The goal of `raise_flag × tag_closed` after `unveil_local` is
`tag J = true → mark I J = true → tag I = true` with `J I` already local,
while the conjunct is `∀ J I, …`. The first matcher alone cannot close
it; `h` applied to the two binders and the two hypotheses can. -/

namespace Shape

#prove_vc CheapRungBindersModel raise_flag tag_closed by
  unveil_local
  all_goals veil_inv_have h := CheapRungBindersModel.tag_closed
  fail_if_success
    all_goals (repeat (first | exact h | exact h .. | intro _))
    done
  all_goals (intro hJ hI; exact h _ _ hJ hI)

end Shape

/-! ## The rung closes frame cells in both shapes -/

namespace Bare

-- Introduced shape, two binders fixed by different hypotheses.
#prove_vc CheapRungBindersModel raise_flag tag_closed by
  veil_solve_frame CheapRungBindersModel.tag_closed

-- Introduced shape, binders fixed by the conclusion.
#prove_vc CheapRungBindersModel raise_flag pair_sym by
  veil_solve_frame CheapRungBindersModel.pair_sym

-- Quantified shape: the first matcher's case.
#prove_vc CheapRungBindersModel link pair_sym by
  veil_solve_frame CheapRungBindersModel.pair_sym

/-- info: 'Bare.raise_flag_tag_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bare.raise_flag_tag_closed

/-- info: 'Bare.raise_flag_pair_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bare.raise_flag_pair_sym

/-- info: 'Bare.link_pair_sym' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bare.link_pair_sym

end Bare

/-! ## Cells that are not frames still decline

`link` writes `mark`, which both invariants below read. The rung must
fail on them — the telescope matcher finds no local hypothesis for the
pre-state `mark` atom — so `first` falls through to the SMT rung. -/

namespace Decline

#prove_vc CheapRungBindersModel link tag_closed by
  fail_if_success veil_solve_frame CheapRungBindersModel.tag_closed
  veil_solve_wp

#prove_vc CheapRungBindersModel link mark_needs_flag

/-- info: 'Decline.link_tag_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Decline.link_tag_closed

/-- info: 'Decline.link_mark_needs_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Decline.link_mark_needs_flag

end Decline

/-! Five attempts — three bare, one under `fail_if_success`, one through
the ladder — of which the three frame cells were won. -/
#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 5 do
    throw <| IO.userError s!"expected 5 cheap-rung attempts, got {attempts}"
  unless wins == 3 do
    throw <| IO.userError s!"expected 3 cheap-rung wins, got {wins}"
