import VeilTest.CheapRungBase

/-! # Cheap non-SMT discharger rung (`veil.vc.cheapRung`)

Each invariant-preservation cell's discharger term is a two-rung ladder,
`by first | veil_solve_frame <invariant> | veil_solve_wp`, inside the
*existing* discharger. This file pins both directions on the model of
`VeilTest/CheapRungBase.lean`:

* `raise_flag × mark_irreflexive` is a **frame** cell — the action writes
  only `flag`, the invariant reads only `mark` — and the cheap rung
  closes it with no solver call at all;
* `link × mark_irreflexive` is **not** framed, the rung fails (it is
  `done`-terminated, so it cannot half-succeed and make `first` commit),
  and the SMT rung proves the cell as before.

Both are kernel-checked with the standard three axioms and no `sorry`,
and the last section pins the property that matters for the trust base:
under `veil.smt.trust true` a cell the rung closes is a real proof, so
the rung *removes* cells from the trusted set. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false
-- NB: this file asserts that the *rung* closes the frame cells, which
-- assumes nothing replays a cached proof of them first. Veil's proof
-- cache is off by default, so there is nothing to switch off here — but
-- a project that turns it on would see cache hits instead, and the
-- counters below would not move.

open Veil CheapRungModel

/-! ## The rung on its own -/

namespace Bare

-- `raise_flag` writes `flag`; `mark_irreflexive` reads `mark`.
#prove_vc CheapRungModel raise_flag mark_irreflexive by
  veil_solve_frame CheapRungModel.mark_irreflexive

/-- info: 'Bare.raise_flag_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bare.raise_flag_mark_irreflexive

end Bare

/-! ## The ladder, both directions -/

namespace Ladder

-- Frame cell: the default `#prove_vc` term is the ladder, and the cheap
-- rung wins.
#prove_vc CheapRungModel raise_flag mark_irreflexive

-- Not framed: the rung declines and `veil_solve_wp` proves the cell.
#prove_vc CheapRungModel link mark_irreflexive

/-- info: 'Ladder.raise_flag_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ladder.raise_flag_mark_irreflexive

/-- info: 'Ladder.link_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ladder.link_mark_irreflexive

end Ladder

/-! The counters behind the ⚡ report line (`veil.report.cheapRung`).
Three attempts so far — one bare, two through the ladder — of which the
two frame cells were closed without a solver and the `link` cell fell
through. Both numbers matter: without the wins the rung is dead weight,
and without the fall-through the `done` guard is untested. -/
#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 3 do
    throw <| IO.userError s!"expected 3 cheap-rung attempts, got {attempts}"
  unless wins == 2 do
    throw <| IO.userError s!"expected 2 cheap-rung wins, got {wins}"

/-! ## The rung shrinks the trusted set

`veil.smt.trust true` makes `veil_solve_wp` emit a `sorryAx`-carrying
leaf instead of a reconstructed proof. A cell the cheap rung closes never
reaches that tactic, so it is a real proof even in trusted mode — the
axiom pin below is the standard three, not `sorryAx`. -/

namespace Trusted

set_option veil.smt.trust true
set_option warn.sorry false

#prove_vc CheapRungModel raise_flag mark_irreflexive

/-- info: 'Trusted.raise_flag_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Trusted.raise_flag_mark_irreflexive

end Trusted

/-! ## Turning the rung off restores the SMT-only term -/

namespace RungOff

set_option veil.vc.cheapRung false

#prove_vc CheapRungModel raise_flag mark_irreflexive

/-- info: 'RungOff.raise_flag_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RungOff.raise_flag_mark_irreflexive

end RungOff

/-! With the option off no further attempt was made: still 4 attempts
(the `Trusted` cell added one) and 3 wins. -/
#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 4 do
    throw <| IO.userError s!"expected 4 cheap-rung attempts, got {attempts}"
  unless wins == 3 do
    throw <| IO.userError s!"expected 3 cheap-rung wins, got {wins}"
