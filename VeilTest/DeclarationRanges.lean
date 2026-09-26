import Veil

/-! # Source locations of generated declarations

Every declaration Veil generates records a declaration range — the location
doc-gen4 source links and go-to-definition use. A declaration derived from
one user declaration (an action's `.do`/`.wp`/`.ext` views, an invariant's
locality lemmas, a state field) points at that declaration and selects the
name the user wrote; a declaration a `#`-command assembles from several user
declarations (`Invariants`, `Next`) points at that command. -/

open Lean Elab Command in
/-- For each name: the line its declaration range starts on, and the source
text its selection range covers. -/
elab "#decl_ranges " ids:ident+ : command => do
  let fm ← getFileMap
  for id in ids do
    let n := id.getId
    let msg ← match ← findDeclarationRanges? n with
      | none => pure m!"{n}: no declaration range"
      | some r =>
        let sel := String.Pos.Raw.extract fm.source (fm.ofPosition r.selectionRange.pos) (fm.ofPosition r.selectionRange.endPos)
        pure m!"{n}: line {r.range.pos.line}, selects `{sel}`"
    logInfo msg

set_option linter.unusedVariables false

veil module RangeMod

type node
enum color = { red, green }

relation r : node → Bool
relation frozen : node → Bool
individual c : Nat
immutable individual bound : Nat

#gen_state

ghost relation both (n : node) := r n ∧ frozen n

assumption [bound_pos] bound > 0

after_init {
  r N := false
  frozen N := false
  c := 0
}

procedure bump {
  c := c + 1
}

action mark (n : node) {
  require ¬ frozen n
  r n := true
  bump
}

action freeze (n : node) {
  require r n
  frozen n := true
}

transition keep {
  r = r' ∧ frozen = frozen' ∧ c = c'
}

invariant [frozen_r] frozen N → r N

#gen_spec

end RangeMod

/-! ## Declarations derived from one user declaration point at it -/

/--
info: RangeMod.State.r: line 33, selects `r`
---
info: RangeMod.Instantiation.node: line 30, selects `node`
---
info: RangeMod.Theory.bound: line 36, selects `bound`
---
info: RangeMod.both: line 40, selects `both`
---
info: RangeMod.bound_pos: line 42, selects `bound_pos`
---
info: RangeMod.initializer: line 44, selects `after_init`
---
info: RangeMod.bump: line 50, selects `bump`
---
info: RangeMod.mark: line 54, selects `mark`
---
info: RangeMod.mark.do: line 54, selects `mark`
---
info: RangeMod.mark.ext: line 54, selects `mark`
---
info: RangeMod.mark.wp: line 54, selects `mark`
---
info: RangeMod.mark.ext.tr: line 54, selects `mark`
---
info: RangeMod.keep: line 65, selects `keep`
---
info: RangeMod.keep.ext.tr: line 65, selects `keep`
---
info: RangeMod.frozen_r: line 69, selects `frozen_r`
---
info: RangeMod.frozen_r.local_abstract_eq: line 69, selects `frozen_r`
-/
#guard_msgs in
#decl_ranges RangeMod.State.r RangeMod.Instantiation.node RangeMod.Theory.bound
  RangeMod.both RangeMod.bound_pos RangeMod.initializer RangeMod.bump
  RangeMod.mark RangeMod.mark.do RangeMod.mark.ext RangeMod.mark.wp RangeMod.mark.ext.tr
  RangeMod.keep RangeMod.keep.ext.tr
  RangeMod.frozen_r RangeMod.frozen_r.local_abstract_eq

/-! ## Constructors and class members belong to the generating command -/

/--
info: RangeMod.State.mk: line 38, selects `#gen_state`
---
info: RangeMod.LocalRProp.core: line 38, selects `#gen_state`
---
info: RangeMod.color_EnumClass.complete: line 31, selects `color`
-/
#guard_msgs in
#decl_ranges RangeMod.State.mk RangeMod.LocalRProp.core RangeMod.color_EnumClass.complete

/-! ## Assembled declarations point at the assembling command -/

/--
info: RangeMod.Invariants: line 71, selects `#gen_spec`
---
info: RangeMod.Next: line 71, selects `#gen_spec`
-/
#guard_msgs in
#decl_ranges RangeMod.Invariants RangeMod.Next
