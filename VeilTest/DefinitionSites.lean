import Veil

/-! # Definition sites of Veil declarations

The name a Veil command declares carries a binder `TermInfo` for the
declared constant, and that constant's selection range is the name — the
two facts hover and find-references at the declaration rely on, and what
SubVerso (hence Verso's per-declaration anchors) takes as a definition site.
`#def_sites in cmd` elaborates `cmd` and lists the identifiers its info trees
make definition sites under SubVerso's rule
(`SubVerso.Highlighting.isDefinition`): a `TermInfo` whose expression is a
constant, on a source identifier whose range is that constant's declaration
range or selection range. -/

namespace DefinitionSites
open Lean Elab Command

partial def termInfos : InfoTree → Array TermInfo
  | .context _ t => termInfos t
  | .node (.ofTermInfo ti) cs => #[ti] ++ cs.toArray.flatMap termInfos
  | .node _ cs => cs.toArray.flatMap termInfos
  | .hole _ => #[]

/-- See the module docstring. -/
elab "#def_sites " "in " cmd:command : command => do
  let before := (← get).infoState.trees.size
  elabCommand cmd
  let trees := (← get).infoState.trees.toArray.extract before
  let mut seen : Std.HashSet (Name × Nat) := {}
  for ti in trees.flatMap termInfos do
    let .const n _ := ti.expr.consumeMData | continue
    -- Only identifiers the user wrote are tokens a renderer can anchor.
    unless ti.stx.isIdent && ti.stx.getHeadInfo matches .original .. do continue
    let some range ← getDeclarationRange? ti.stx | continue
    let some dr ← findDeclarationRanges? n | continue
    unless range == dr.range || range == dr.selectionRange do continue
    if seen.contains (n, range.pos.line) then continue
    seen := seen.insert (n, range.pos.line)
    logInfo m!"`{ti.stx.getId}` (line {range.pos.line}) defines {n}"

end DefinitionSites

set_option linter.unusedVariables false

veil module SiteMod

type node

relation r : node → Bool
relation frozen : node → Bool
immutable individual bound : Nat

/--
info: `bound` (line 51) defines SiteMod.Theory.bound
---
info: `r` (line 49) defines SiteMod.State.r
---
info: `frozen` (line 50) defines SiteMod.State.frozen
-/
#guard_msgs in
#def_sites in
#gen_state

/-- info: `both` (line 67) defines SiteMod.both -/
#guard_msgs in
#def_sites in
ghost relation both (n : node) := r n ∧ frozen n

/-- info: `bound_pos` (line 72) defines SiteMod.bound_pos -/
#guard_msgs in
#def_sites in
assumption [bound_pos] bound > 0

after_init {
  r N := false
  frozen N := false
}

/-- info: `bump` (line 82) defines SiteMod.bump -/
#guard_msgs in
#def_sites in
procedure bump {
  pure ()
}

/-- info: `mark` (line 89) defines SiteMod.mark -/
#guard_msgs in
#def_sites in
action mark (n : node) {
  require ¬ frozen n
  r n := true
  bump
}

/-- info: `withSpec` (line 98) defines SiteMod.withSpec -/
#guard_msgs in
#def_sites in
action withSpec (n : node)
  requires True
  ensures True
{
  pure ()
}

/-- info: `keep` (line 108) defines SiteMod.keep -/
#guard_msgs in
#def_sites in
transition keep {
  r = r' ∧ frozen = frozen'
}

/-- info: `frozen_r` (line 115) defines SiteMod.frozen_r -/
#guard_msgs in
#def_sites in
invariant [frozen_r] frozen N → r N

-- An unnamed assertion writes no name, so it has no definition site.
#guard_msgs in
#def_sites in
safety True

#gen_spec

end SiteMod
