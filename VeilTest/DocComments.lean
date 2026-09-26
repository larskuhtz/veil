import Veil

/-! # Doc comments on Veil declarations

A doc comment may precede any Veil command that declares something, and
becomes the docstring of the constant the declaration generates: an action's,
a procedure's, a transition's, a ghost definition's or an assertion's own
constant; `State.<f>` for a mutable state component and `Theory.<f>` for an
immutable one; `Instantiation.<n>` for a sort, an enum, a parameter or an
instantiated class. Those structure fields are generated with the state, so
their docstrings arrive then. `#docs_of` prints the docstring of each named
constant. -/

namespace DocComments
open Lean Elab Command

/-- See the module docstring. -/
elab "#docs_of " ns:ident names:ident* : command => do
  for n in names do
    let c := ns.getId ++ n.getId
    match ← findDocString? (← getEnv) c with
    | some d => logInfo m!"{c}: {d.trimAscii}"
    | none => logInfo m!"{c}: none"

end DocComments

class Marked (t : Type) where
  marked : t → Prop

set_option linter.unusedVariables false

veil module DocMod

/-- sort -/
type node

/-- enum -/
enum color = { red, green }

/-- param -/
param bound : Nat

/-- instantiated class -/
instantiate mk : Marked node

/-- mutable relation -/
relation r : node → Bool

/-- immutable individual -/
immutable individual leader : node

/-- mutable function -/
function paint : node → color

/-- Markdown survives: **bold**, `code`. -/
relation plain : node → Bool

-- Not documented: stays without a docstring.
relation bare : node → Bool

-- State components are fields of structures generated with the state, so
-- their docstrings are not there yet.
/--
info: DocMod.State.r: none
---
info: DocMod.Instantiation.node: none
-/
#guard_msgs in
#docs_of DocMod State.r Instantiation.node

/-- ghost relation -/
ghost relation both (n : node) := r n ∧ plain n

/-- initializer -/
after_init {
  r N := false
  plain N := false
  bare N := false
}

/-- procedure -/
procedure bump {
  pure ()
}

/-- action -/
action mark (n : node) {
  r n := true
  bump
}

/-- action with a specification -/
action withSpec (n : node)
  requires True
  ensures True
{
  pure ()
}

/-- transition -/
transition keep {
  r = r' ∧ plain = plain' ∧ bare = bare'
}

/-- named invariant -/
invariant [r_refl] r N → r N

/-- unnamed safety property -/
safety True

/-- assumption -/
assumption [bound_pos] bound > 0

/-- step property -/
step_property [r_mono] { r N → r' N }

-- Inside `set_option … in`, the doc comment goes with the declaration.
set_option linter.unusedVariables false in
/-- scoped invariant -/
invariant [plain_refl] plain N → plain N

-- In front of `… in`, a doc comment is an error that says where it goes.
/--
error: unexpected doc comment: write it after `… in`, directly in front of the declaration it documents
-/
#guard_msgs in
/-- misplaced -/
set_option linter.unusedVariables false in
invariant [bare_refl] bare N → bare N

-- A doc comment on a command that declares nothing is an error.
/--
error: unexpected doc comment: it documents a declaration, and this command declares nothing
-/
#guard_msgs in
/-- not a declaration -/
open_isolate DocMod

-- An ordinary Lean declaration still takes its doc comment itself.
/-- a Lean definition -/
def helper : Nat := 1

#gen_spec

/--
info: DocMod.Instantiation.node: sort
---
info: DocMod.Instantiation.color: enum
---
info: DocMod.Instantiation.bound: param
---
info: DocMod.Instantiation.mk: instantiated class
---
info: DocMod.State.r: mutable relation
---
info: DocMod.Theory.leader: immutable individual
---
info: DocMod.State.paint: mutable function
---
info: DocMod.State.plain: Markdown survives: **bold**, `code`.
---
info: DocMod.State.bare: none
---
info: DocMod.both: ghost relation
---
info: DocMod.initializer: initializer
---
info: DocMod.bump: procedure
---
info: DocMod.mark: action
---
info: DocMod.withSpec: action with a specification
---
info: DocMod.keep: transition
---
info: DocMod.r_refl: named invariant
---
info: DocMod.safety_0: unnamed safety property
---
info: DocMod.bound_pos: assumption
---
info: DocMod.r_mono: step property
---
info: DocMod.plain_refl: scoped invariant
---
info: DocMod.helper: a Lean definition
-/
#guard_msgs in
#docs_of DocMod Instantiation.node Instantiation.color Instantiation.bound Instantiation.mk
  State.r Theory.leader State.paint State.plain State.bare
  both initializer bump mark withSpec keep r_refl safety_0 bound_pos r_mono plain_refl helper

-- Only the declared constant carries the docstring, not what is derived
-- from it.
/--
info: DocMod.initializer.do: none
---
info: DocMod.initializer.ext: none
---
info: DocMod.mark.do: none
---
info: DocMod.mark.ext: none
-/
#guard_msgs in
#docs_of DocMod initializer.do initializer.ext mark.do mark.ext

end DocMod
