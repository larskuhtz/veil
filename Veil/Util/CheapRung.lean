import Lean
import Veil.Base

/-! # Cheap-rung counters (`veil.vc.cheapRung`)

Each VC's discharger term is a two-rung ladder,
`by first | veil_solve_frame <invariant> | veil_solve_wp`: a cheap
non-SMT tactic is tried first and the SMT tactic runs only if it fails.
One `first` means one attempt from the manager's point of view, so the
per-rung attribution the discharger *names* carry (`…_0_WP`, `…_tr_0_TR`)
no longer distinguishes the two branches — and the hit rate is exactly the
number that says whether the ladder is worth its cost.

These process-cumulative counters recover it. `veil_solve_frame` records
an attempt on entry and a win only after it has actually closed the goal;
the sweep summary prints one ⚡ line (`formatCheapRungNote`) and
`trace.veil.cheapRung` carries the per-cell detail (which conjunct was
projected, or why the rung declined).

Counters only — nothing here is consulted by any proof. -/

namespace Veil.CheapRung

/-- (attempts, wins) of the cheap rung in this process. Read by the
sweep-results summary line and by tests; per-attempt detail is on
`trace.veil.cheapRung`. -/
initialize stats : IO.Ref (Nat × Nat) ← IO.mkRef (0, 0)

/-- Record an entry into the cheap rung (before it can fail). -/
def recordAttempt : IO Unit :=
  stats.modify fun (a, w) => (a + 1, w)

/-- Record a cheap-rung win — the goal is closed and no solver ran. -/
def recordWin : IO Unit :=
  stats.modify fun (a, w) => (a, w + 1)

def statsAttempts : IO Nat := return (← stats.get).1
def statsWins : IO Nat := return (← stats.get).2

end Veil.CheapRung
