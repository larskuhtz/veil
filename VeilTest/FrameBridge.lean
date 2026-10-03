import VeilTest.CheapRungBase

/-! # The per-action frame bridge (`veil.vc.frameBridge`)

`#prove_action` emits one kernel-checked theorem per action,
`<action>.ext.frame_bridge` — the local-WP bridge run once over an abstract
postcondition — and the cheap rung of each frame cell instantiates it,
with the postcondition's `LocalRProp` instance passed by name, and closes
the cell by projection and `exact`, without simp (the simps are the
fallback). This file pins, on the model of `VeilTest/CheapRungBase.lean`:

* `raise_flag`: the theorem is emitted, and the **frame** cell
  `raise_flag × mark_irreflexive` is closed by the rung through it (so is
  `mark_needs_flag`, which `flag n := true` cannot break);
* `initializer` (precondition `True`): the theorem is emitted as well, and
  both of its cells go to the rung (through the simp fallback: the
  initializer writes every field);
* `link × mark_irreflexive` is **not** a frame cell: the rung declines and
  the solver proves it, so its proof does not use the bridge theorem;
* every theorem — the bridges and the cells — has the standard three
  axioms;
* with the option off, a cell does not use the bridge theorem. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false

open Veil CheapRungModel

def rungStats : IO (Nat × Nat) := Veil.CheapRung.stats.get

/-- Whether the persisted theorem `thm` refers to the constant `c`. -/
def proofUses (thm c : Lean.Name) : Lean.Elab.Command.CommandElabM Bool := do
  let some (.thmInfo v) := (← Lean.getEnv).find? thm
    | throwError "{thm} is not a theorem in scope"
  return (v.value.find? (·.isConstOf c)).isSome

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
  unless ← proofUses `Bridge.raise_flag_mark_irreflexive `CheapRungModel.raise_flag.ext.frame_bridge do
    throwError "the frame cell does not use the frame-bridge theorem"

/-! Two rung attempts, two wins. -/
#eval show IO Unit from do
  let (attempts, wins) ← rungStats
  unless attempts == 2 && wins == 2 do
    throw <| IO.userError s!"expected 2 attempts / 2 wins, got {attempts} / {wins}"

#prove_action CheapRungModel initializer

/-- info: 'CheapRungModel.initializer.ext.frame_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CheapRungModel.initializer.ext.frame_bridge

/-- info: 'Bridge.initializer_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.initializer_mark_irreflexive

#eval show IO Unit from do
  let (attempts, wins) ← rungStats
  unless attempts == 4 && wins == 4 do
    throw <| IO.userError s!"expected 4 attempts / 4 wins, got {attempts} / {wins}"

#prove_action CheapRungModel link

/-- info: 'Bridge.link_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Bridge.link_mark_irreflexive

-- Not a frame cell: the rung declined, the solver proved it.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  if ← proofUses `Bridge.link_mark_irreflexive `CheapRungModel.link.ext.frame_bridge then
    throwError "the non-frame cell's proof uses the frame-bridge theorem"

#eval show IO Unit from do
  let (attempts, _) ← rungStats
  unless attempts == 6 do
    throw <| IO.userError s!"expected 6 attempts, got {attempts}"

end Bridge

/-! ## Off: the previous rung -/

namespace Off

set_option veil.vc.frameBridge false

#prove_action CheapRungModel raise_flag

#eval show Lean.Elab.Command.CommandElabM Unit from do
  if ← proofUses `Off.raise_flag_mark_irreflexive `CheapRungModel.raise_flag.ext.frame_bridge then
    throwError "the frame-bridge theorem was used with the option off"

/-- info: 'Off.raise_flag_mark_irreflexive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Off.raise_flag_mark_irreflexive

end Off
