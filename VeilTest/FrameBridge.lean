import VeilTest.CheapRungBase

/-! # The per-action frame bridge (`veil.vc.frameBridge`)

`#prove_action` emits one kernel-checked theorem per action,
`<action>.ext.frame_bridge` — the local-WP bridge run once over an abstract
postcondition — and the cheap rung of each frame cell instantiates it,
with the postcondition's `LocalRProp` instance passed by name, and closes
the cell by projection and `exact`, without simp. This file pins, on the
model of `VeilTest/CheapRungBase.lean`:

* `raise_flag`: the theorem is emitted; the **frame** cell
  `raise_flag × mark_irreflexive` is closed by the rung through it; the
  touched cell `raise_flag × mark_needs_flag` **falls through** to the
  solver;
* `initializer` (precondition `True`): the theorem is emitted as well, and
  its cell `mark_irreflexive`, which the simp fallback closes, still goes to
  the rung;
* every theorem — the bridges and the cells — has the standard three
  axioms;
* with the option off, no theorem is emitted. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false

open Veil CheapRungModel

def rungStats : IO (Nat × Nat) := Veil.CheapRung.stats.get

namespace Bridge

#prove_action CheapRungModel raise_flag

/-- info: 'CheapRungModel.raise_flag.ext.frame_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CheapRungModel.raise_flag.ext.frame_bridge

/-- info: 'Bridge.raise_flag_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.raise_flag_mark_irreflexive

/-- info: 'Bridge.raise_flag_mark_needs_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.raise_flag_mark_needs_flag

-- The frame cell's proof goes through the bridge theorem.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let some ci := (← Lean.getEnv).find? `Bridge.raise_flag_mark_irreflexive
    | throwError "missing cell theorem"
  let .thmInfo v := ci | throwError "the cell is not a theorem"
  unless (v.value.find? (·.isConstOf `CheapRungModel.raise_flag.ext.frame_bridge)).isSome do
    throwError "the frame cell does not use the frame-bridge theorem"

/-! Two rung attempts (`mark_irreflexive`, `mark_needs_flag`), one win:
the frame cell. -/
#eval show IO Unit from do
  let (attempts, wins) ← rungStats
  unless attempts == 2 && wins == 1 do
    throw <| IO.userError s!"expected 2 attempts / 1 win, got {attempts} / {wins}"

#prove_action CheapRungModel initializer

/-- info: 'CheapRungModel.initializer.ext.frame_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CheapRungModel.initializer.ext.frame_bridge

/-- info: 'Bridge.initializer_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.initializer_mark_irreflexive

/-! Both initializer cells are closed by the rung (through the simp
fallback: the initializer writes every field, so neither is a frame). -/
#eval show IO Unit from do
  let (attempts, wins) ← rungStats
  unless attempts == 4 && wins == 3 do
    throw <| IO.userError s!"expected 4 attempts / 3 wins, got {attempts} / {wins}"

end Bridge

/-! ## Off: no theorem, the previous rung -/

namespace Off

set_option veil.vc.frameBridge false

#prove_action CheapRungModel link

#eval show Lean.Elab.Command.CommandElabM Unit from do
  if (← Lean.getEnv).contains `CheapRungModel.link.ext.frame_bridge then
    throwError "a frame-bridge theorem was emitted with the option off"

/-- info: 'Off.link_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Off.link_mark_irreflexive

end Off
