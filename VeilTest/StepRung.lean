import VeilTest.StepPropertyBase

/-! # Cheap non-SMT rung for `step_property` cells (`veil.vc.cheapRung`)

A step cell's discharger term is the ladder
`by first | veil_solve_step_frame | veil_solve_step`. The cheap rung runs
the step route with the invariant clump (`hinv`) and the assumptions
(`has`) cleared, and finishes with `grind`. This file pins both directions
on the model of `VeilTest/StepPropertyBase.lean`:

* `mark × frozen_mono` is a **frame** cell — `mark` writes `r` only — and
  the rung closes it;
* `freeze × frozen_mono` is a **writer** cell — `freeze` sets `frozen` —
  and the rung still closes it, from the update equation alone;
* `mark × frozen_stays_r` needs the **invariant** `frozen_r` at the
  pre-state (a frozen `n` with `r n` false would be a counterexample once
  `hinv` is gone): the rung declines, and the solver route proves it.

All three are kernel-checked with the standard three axioms. The last
section pins the rung's heartbeat budget (`veil.vc.stepRungHeartbeats`):
an overrun is a decline like any other, and the solver route proves the
cell. `VeilTest/StepRungBudget.lean` pins the same for an overrun in the
middle of a long `grind` run. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false

open Veil StepRegMod

namespace Bare

#prove_vc StepRegMod mark frozen_mono by
  veil_solve_step_frame

#prove_vc StepRegMod freeze frozen_mono by
  veil_solve_step_frame

/-- info: 'Bare.freeze_frozen_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bare.freeze_frozen_mono

end Bare

namespace Ladder

-- The default `#prove_vc` term is the ladder.
#prove_vc StepRegMod mark frozen_mono
#prove_vc StepRegMod mark frozen_stays_r

/-- info: 'Ladder.mark_frozen_stays_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ladder.mark_frozen_stays_r

end Ladder

/-! Four attempts — two bare, two through the ladder — of which three
closed without a solver and `mark × frozen_stays_r` fell through. -/
#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 4 do
    throw <| IO.userError s!"expected 4 cheap-rung attempts, got {attempts}"
  unless wins == 3 do
    throw <| IO.userError s!"expected 3 cheap-rung wins, got {wins}"

/-! ## The rung shrinks the trusted set

Under `veil.smt.trust true` a cell the rung closes never reaches the
solver, so it is a real proof — the standard three axioms, not `sorryAx`. -/

namespace Trusted

set_option veil.smt.trust true
set_option warn.sorry false

#prove_vc StepRegMod freeze frozen_mono

/-- info: 'Trusted.freeze_frozen_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Trusted.freeze_frozen_mono

end Trusted

/-! ## Turning the rung off restores the solver-only term -/

namespace RungOff

set_option veil.vc.cheapRung false

#prove_vc StepRegMod mark frozen_mono

end RungOff

#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 5 do
    throw <| IO.userError s!"expected 5 cheap-rung attempts, got {attempts}"
  unless wins == 4 do
    throw <| IO.userError s!"expected 4 cheap-rung wins, got {wins}"

/-! ## An overrun of the heartbeat budget is a decline

Exceeding `maxHeartbeats` is a *runtime* exception, which `first | … | …`
does not catch; the rung converts it into an ordinary failure, so the
ladder falls through. The budget counts heartbeats, not wall time, so which
cells overrun is deterministic. -/

namespace Budget

set_option veil.vc.stepRungHeartbeats 1

-- The rung wins this cell under the default budget (`Bare` above); with a
-- budget of 1 it overruns at once, and `veil_solve_step` proves the cell.
#prove_vc StepRegMod freeze frozen_mono

/-- info: 'Budget.freeze_frozen_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Budget.freeze_frozen_mono

end Budget

/-! One more attempt, no more wins: the overrun fell through. -/
#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 6 do
    throw <| IO.userError s!"expected 6 cheap-rung attempts, got {attempts}"
  unless wins == 4 do
    throw <| IO.userError s!"expected 4 cheap-rung wins, got {wins}"
