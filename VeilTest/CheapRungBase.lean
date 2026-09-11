import Veil

/-! # Cheap non-SMT discharger rung (`veil.vc.cheapRung`) — the model

Two relations and two actions, arranged so that the (action, property)
grid contains both kinds of cell the ladder has to tell apart:

|                     | `mark_irreflexive` (reads `mark`) | `mark_needs_flag` (reads both) |
|---------------------|-----------------------------------|--------------------------------|
| `raise_flag` (writes `flag`) | **frame** — cheap rung closes it | touched — falls through to SMT |
| `link` (writes `mark`)       | touched — falls through to SMT   | touched — falls through to SMT |

`VeilTest/CheapRung.lean` checks both kinds cross-file, where the
discharge term is built from this registry. The in-file sweep below is
the same check on the in-file path. -/

set_option linter.unusedVariables false
set_option veil.gen.vcRegistry true
set_option veil.smt.trust false

veil module CheapRungModel

type node

relation flag : node -> Bool
relation mark : node -> node -> Bool

#gen_state

after_init {
  flag N := false
  mark M N := false
}

action raise_flag (n : node) {
  flag n := true
}

action link (m n : node) {
  require m ≠ n
  require flag m
  mark m n := true
}

invariant [mark_irreflexive] ¬ mark N N
invariant [mark_needs_flag] mark M N → flag M

#gen_spec

/--
info: Initialization must establish the invariant:
  doesNotThrow ... ✅
  mark_irreflexive ... ✅
  mark_needs_flag ... ✅
The following set of actions must preserve the invariant and successfully terminate:
  raise_flag
    doesNotThrow ... ✅
    mark_irreflexive ... ✅
    mark_needs_flag ... ✅
  link
    doesNotThrow ... ✅
    mark_irreflexive ... ✅
    mark_needs_flag ... ✅
-/
#guard_msgs in
#check_invariants

end CheapRungModel
