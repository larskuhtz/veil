import Veil

/-! # The step rung's heartbeat budget, on a long `grind` run

`veil_solve_step_frame` (`veil.vc.cheapRung`) finishes with `grind` under a
budget of its own, `veil.vc.stepRungHeartbeats`. Exceeding it is a runtime
exception, which `first | … | …` does not catch; the rung turns it into an
ordinary failure, so the ladder falls through to `veil_solve_step`. The
budget counts heartbeats, not wall time, so which cells overrun is
deterministic.

The cell below makes `grind` work: the guard's transitivity and symmetry
have to be chained along five links to show that `a` reaches itself. With
the default budget the rung closes it; with a budget well inside that run it
overruns mid-search and the solver route proves the cell. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.gen.vcRegistry true

veil module StepRungLong

type node

relation r : node → node → Bool
relation s : node → Bool

#gen_state

after_init {
  r N M := false
  s N := false
}

action go (a b c d e f : node) {
  require ∀ x y z, r x y ∧ r y z → r x z
  require ∀ x y, r x y → r y x
  require r a b ∧ r b c ∧ r c d ∧ r d e ∧ r e f
  s a := true
}

invariant true

step_property [reach] { s' N → s N ∨ r N N }

#gen_spec

end StepRungLong

open Veil StepRungLong

namespace Long

-- With the default budget the rung wins.
#prove_vc StepRungLong go reach

end Long

namespace LongCapped

-- With a budget well inside `grind`'s run it overruns mid-search, and the
-- solver route proves the cell.
set_option veil.vc.stepRungHeartbeats 100

#prove_vc StepRungLong go reach

/-- info: 'LongCapped.go_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LongCapped.go_reach

end LongCapped

/-! Two attempts and one win: the overrun fell through. -/
#eval show IO Unit from do
  let (attempts, wins) ← Veil.CheapRung.stats.get
  unless attempts == 2 do
    throw <| IO.userError s!"expected 2 cheap-rung attempts, got {attempts}"
  unless wins == 1 do
    throw <| IO.userError s!"expected 1 cheap-rung win, got {wins}"
