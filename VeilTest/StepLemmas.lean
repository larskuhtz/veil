import Veil

/-! # Generated step lemmas (`veil.gen.stepLemmas`)

At `#gen_spec`, Veil derives from every imperative action's pre-computed
transition the frame lemma `<action>.frame_<f>` or the monotonicity lemma
`<action>.mono_<f>` per state component, the whole-system `<f>.mono` when
every action has one of the two, and `<f>.init` from the initializer — all
kernel-checked, none assumed. This module has one action per recognised
update shape (plain `true` write, one-armed `if`, two-armed `if` with a
different write in `else`, `pick`, bulk write, `false` write, computed
write, write through a procedure) plus one `transition`-syntax action, which
is outside the recognised shape and blocks every whole-system lemma.
Emission is silent: `#gen_spec` produces no message. -/

set_option linter.unusedVariables false

veil module StepLemmasMod

type node

relation r : node → Bool
relation q : node → node → Bool
individual c : Nat
individual flag : Bool

#gen_state

after_init {
  r N := false
  q N M := false
  c := 0
  flag := false
}

action cond_write (n : node) {
  if flag then
    r n := true
}

action cond_else (n : node) {
  if flag then
    r n := true
  else
    c := c + 1
}

action picky (n : node) {
  let x ← pick node
  q n x := true
}

action bulk {
  r N := true
}

action neg (n : node) {
  r n := false
}

action computed (n : node) {
  r n := r n && flag
}

procedure helper (n : node) {
  q n n := true
}

action via_proc (n : node) {
  helper n
}

transition byz {
  ∀ N, (r N → r' N)
}

invariant true

#guard_msgs in
#gen_spec

end StepLemmasMod

/-! ## What exists, on the standard axioms -/

/-- info: 'StepLemmasMod.cond_write.tr_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.cond_write.tr_of_step
/-- info: 'StepLemmasMod.cond_write.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.cond_write.frame
/-- info: 'StepLemmasMod.cond_write.frame_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.cond_write.frame_q
/-- info: 'StepLemmasMod.cond_write.mono_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.cond_write.mono_r
/-- info: 'StepLemmasMod.cond_else.frame_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.cond_else.frame_q
/-- info: 'StepLemmasMod.cond_else.mono_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.cond_else.mono_r
/-- info: 'StepLemmasMod.picky.frame_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.picky.frame_r
/-- info: 'StepLemmasMod.picky.mono_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.picky.mono_q
/-- info: 'StepLemmasMod.bulk.mono_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.bulk.mono_r
/-- info: 'StepLemmasMod.neg.frame_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.neg.frame_q
/-- info: 'StepLemmasMod.computed.frame_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.computed.frame_c
/-- info: 'StepLemmasMod.via_proc.mono_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.via_proc.mono_q
/-- info: 'StepLemmasMod.via_proc.frame_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.via_proc.frame_r
/-- info: 'StepLemmasMod.r.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.r.init
/-- info: 'StepLemmasMod.q.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.q.init
/-- info: 'StepLemmasMod.c.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.c.init
/-- info: 'StepLemmasMod.flag.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasMod.flag.init

/-! ## What must not exist -/

-- A `false` write is not monotone …
/-- error: Unknown constant `StepLemmasMod.neg.mono_r` -/
#guard_msgs in
#print axioms StepLemmasMod.neg.mono_r
-- … nor is a computed write; and a written field has no frame.
/-- error: Unknown constant `StepLemmasMod.computed.mono_r` -/
#guard_msgs in
#print axioms StepLemmasMod.computed.mono_r
/-- error: Unknown constant `StepLemmasMod.cond_write.frame_r` -/
#guard_msgs in
#print axioms StepLemmasMod.cond_write.frame_r
-- The counter is incremented, not set to a literal.
/-- error: Unknown constant `StepLemmasMod.cond_else.mono_c` -/
#guard_msgs in
#print axioms StepLemmasMod.cond_else.mono_c
-- A `transition`-syntax action gets nothing …
/-- error: Unknown constant `StepLemmasMod.byz.frame_q` -/
#guard_msgs in
#print axioms StepLemmasMod.byz.frame_q
-- … and blocks every whole-system lemma (`q` would otherwise qualify).
/-- error: Unknown constant `StepLemmasMod.q.mono` -/
#guard_msgs in
#print axioms StepLemmasMod.q.mono
/-- error: Unknown constant `StepLemmasMod.r.mono` -/
#guard_msgs in
#print axioms StepLemmasMod.r.mono

/-! ## Consumers apply the lemmas directly -/

section
variable {node : Type} [Inhabited node]

example {th : StepLemmasMod.Theory node}
    {s s' : StepLemmasMod.State (StepLemmasMod.FieldAbstractType node)} {n : node}
    (h : (StepLemmasMod.relationalTransitionSystem node).tr th s (.picky n) s')
    (x y : node) (hq : s.q x y = true) : s'.q x y = true :=
  StepLemmasMod.picky.mono_q h x y hq

example {th : StepLemmasMod.Theory node}
    {s s' : StepLemmasMod.State (StepLemmasMod.FieldAbstractType node)} {n : node}
    (h : (StepLemmasMod.relationalTransitionSystem node).tr th s (.neg n) s')
    (x y : node) : s'.q x y = true ↔ s.q x y = true := by
  rw [StepLemmasMod.neg.frame_q h]

/-- A downstream view through `get` at the abstract representation (with the
classical decidability instances the transition system bakes in) consumes the
lemmas by definitional unfolding, with no hand-written evaluation. -/
noncomputable abbrev Q (st : StepLemmasMod.State (StepLemmasMod.FieldAbstractType node))
    (x y : node) : Prop :=
  @Veil.FieldRepresentation.get _ _ _ (@StepLemmasMod.instAbstractFieldRepresentation node
    (fun a b => Classical.propDecidable (a = b)) StepLemmasMod.State.Label.q) st.q x y = true

example {th : StepLemmasMod.Theory node}
    {s s' : StepLemmasMod.State (StepLemmasMod.FieldAbstractType node)} {n : node}
    (h : (StepLemmasMod.relationalTransitionSystem node).tr th s (.via_proc n) s')
    (x y : node) (hq : Q s x y) : Q s' x y :=
  StepLemmasMod.via_proc.mono_q h x y hq

example {th : StepLemmasMod.Theory node}
    {s : StepLemmasMod.State (StepLemmasMod.FieldAbstractType node)}
    (h : (StepLemmasMod.relationalTransitionSystem node).init th s) (x y : node) : ¬ Q s x y :=
  fun hq => Bool.false_ne_true ((StepLemmasMod.q.init h x y).symm.trans hq)

end

/-! ## Without a `transition`, the whole-system lemmas exist -/

veil module StepLemmasImperative

type node

relation r : node → Bool
relation q : node → node → Bool

#gen_state

after_init {
  r N := false
  q N M := false
}

action mark (n : node) {
  r n := true
}

action link (n m : node) {
  require r n
  q n m := true
}

action unmark (n : node) {
  r n := false
}

invariant true

#guard_msgs in
#gen_spec

end StepLemmasImperative

-- `q` is only ever set to `true` (or left alone) by every action.
/-- info: 'StepLemmasImperative.q.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasImperative.q.mono
-- `r` is set to `false` by `unmark`: no whole-system lemma.
/-- error: Unknown constant `StepLemmasImperative.r.mono` -/
#guard_msgs in
#print axioms StepLemmasImperative.r.mono

section
variable {node : Type} [Inhabited node]

example {th : StepLemmasImperative.Theory node}
    {s s' : StepLemmasImperative.State (StepLemmasImperative.FieldAbstractType node)}
    {l : StepLemmasImperative.Label node}
    (h : (StepLemmasImperative.relationalTransitionSystem node).tr th s l s')
    (x y : node) (hq : s.q x y = true) : s'.q x y = true :=
  StepLemmasImperative.q.mono h x y hq

end

/-! ## The option turns the derivation off -/

veil module StepLemmasOff

type node

relation r : node → Bool

#gen_state

after_init {
  r N := false
}

action mark (n : node) {
  r n := true
}

invariant true

set_option veil.gen.stepLemmas false in
#guard_msgs in
#gen_spec

end StepLemmasOff

/-- error: Unknown constant `StepLemmasOff.mark.mono_r` -/
#guard_msgs in
#print axioms StepLemmasOff.mark.mono_r
/-- error: Unknown constant `StepLemmasOff.r.init` -/
#guard_msgs in
#print axioms StepLemmasOff.r.init

/-! ## Initial values: an enum-valued function, a `pick`ed initial value, a numeral -/

veil module StepLemmasInit

type node
enum phase = {idle, busy}

function kind : node → phase
relation chosen : node → Bool
individual count : Nat

#gen_state

after_init {
  kind N := idle
  chosen := *
  count := 0
}

action work (n : node) {
  kind n := busy
}

invariant true

#guard_msgs in
#gen_spec

end StepLemmasInit

-- The enum constant is a module parameter's projection; the lemma states it.
/-- info: 'StepLemmasInit.kind.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasInit.kind.init
/-- info: 'StepLemmasInit.count.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasInit.count.init
/-- info: 'StepLemmasInit.work.frame_chosen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms StepLemmasInit.work.frame_chosen
-- A `pick`ed initial value is not a literal.
/-- error: Unknown constant `StepLemmasInit.chosen.init` -/
#guard_msgs in
#print axioms StepLemmasInit.chosen.init

section
variable {node phase : Type} [Inhabited node] [Inhabited phase] [StepLemmasInit.phase_EnumClass phase]

example {th : StepLemmasInit.Theory node phase}
    {s : StepLemmasInit.State (StepLemmasInit.FieldAbstractType node phase)}
    (h : (StepLemmasInit.relationalTransitionSystem node phase).init th s) (n : node) :
    s.kind n = StepLemmasInit.phase_EnumClass.idle :=
  StepLemmasInit.kind.init h n

end
