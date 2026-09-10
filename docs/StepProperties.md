# Step lemmas and step properties

*Design note, written against the fork at `8a2f00f7` (Lean 4.32). Status:
Part I (generated step lemmas) is implemented in
`Veil/Frontend/DSL/Module/StepLemmas.lean`; Part II (`step_property`) is
implemented across the assertion, VC-generation, tactic and composition
layers as described here (§3, with the deviations noted in §3.9); Part III
is the declared next step.*

This note covers three related additions to Veil, in the order they are to
be built:

1. **Generated step lemmas** — per action and per state component, theorems
   derived from the action's pre-computed transition: "this action leaves
   `f` unchanged" (frame), "this action only ever sets `f` to `true`"
   (monotonicity), and the whole-system consequences of these.
2. **`step_property`** — a two-state property kind: a proposition over a
   pre-state and a post-state, checked by the solver once per action, in the
   VC grid and in the persistent registry, exactly as invariants are.
3. **Auxiliary (history) state components** — the declared next step, not
   part of this work; recorded here so that the first two are designed to
   accommodate it.

The first two are complementary, not alternatives. Step lemmas are *derived*
from the model with no user input and no solver: they can only state what
the update records literally say. Step properties are *stated* by the user
and *checked* by the solver: they can use the invariants and the guards, and
so cover everything the first cannot (a relation that is frozen once a flag
is set, a property that needs an invariant of the pre-state). Downstream
consumers that assemble a contract from a module today prove both kinds by
hand, action by action, from the same raw material — the generated
transition bodies. That raw material is where this note starts.

## 1. The raw material: `<action>.ext.tr`

For every imperative action, `#gen_spec` pre-computes a two-state
transition `<action>.ext.tr : ρ → σ → σ → Prop` as a `reducible`
definition, and proves `<action>.ext.derived_eq :
(<action>.ext args).toTransitionDerived = <action>.ext.tr … args`, the
bridge from the derived transition the assembled `Next`/`relationalTransitionSystem`
use. Both carry the `trSimp` attribute, so
`simp only [M.relationalTransitionSystem, M.Next, M.NextAct] at h; simp only [trSimp] at h`
exposes the transition body of whichever action a hypothesis
`h : (M.relationalTransitionSystem …).tr th s l s'` names, once `l` is
dispatched (`VeilTest/TrSimp.lean`).

The bodies have a small, regular grammar. Measured on the fork by printing
the `tr` definitions of actions written with plain writes, conditional
writes with and without `else`, `pick`, bulk (capitalised) writes, a `false`
write, a shallow `&&` write, and a write through a procedure call
(`Action/Elaborators.lean`, `defineTransition`; the simplifier inlines
procedures and pushes the state equation to the leaves):

```
body ::= leaf
       | guard ∧ body                      -- guards never mention s₁
       | if c then body else body
       | ∃ x, body                         -- from pick / :| / := *
leaf ::= setIn { f₁ := u₁, …, fₙ := uₙ } s₀ = s₁   -- a State.mk application
       | s₀ = s₁                                   -- the else of a one-armed if
uᵢ   ::= (getFrom s₀).fᵢ                           -- unchanged
       | FieldRepresentation.set descr uᵢ           -- written (possibly nested)
descr ::= [(pat₁, fun x₁ … xₖ => v₁), …]           -- a list literal
pat  ::= (some t, …, none, …, ())                  -- one Option per domain position
```

Everything in Part I is decidable from this grammar by inspection of the
`Expr`, and provable from it by a fixed tactic script. Actions written in
`transition` syntax do not have this shape (their `tr` is the user's
relation under `decide (…) = true`, framed by `[unchanged| …]`
conjuncts) and are treated separately below.

Today a consumer that needs a two-state fact about a generated module
writes, per model, a macro exposing the body and a macro evaluating the
field-representation `get`/`set` pair at the canonical representation, and
one theorem per fact with a uniform script over all labels. The 38-action
module in the downstream project has four such theorems and two
initial-state facts; the 7-action one has seven plus one that also needs an
invariant. Part I generates the record-derived ones; Part II makes the
invariant-dependent ones a checked cell.

## 2. Part I — generated step lemmas

### 2.1 What is emitted

For a module `M` with sorts `σ₁ … σₙ`, mutable component `f` of arity `k`,
and action `a` with arguments `args`, at the *canonical* instantiation —
the one `M.relationalTransitionSystem` fixes: `th : M.Theory σ…`,
`s s' : M.State (M.FieldAbstractType σ…)` — the following theorems, all
in the module's namespace:

| Name | Statement | Emitted when |
|---|---|---|
| `M.a.frame` | `(RTS).tr th s (.a args) s' → s'.f₁ = s.f₁ ∧ … ∧ s'.fₖ = s.fₖ` | the conjunction over every field `a` leaves unchanged; the one destructuring proof per action (§2.4) |
| `M.a.frame_f` | `(RTS).tr th s (.a args) s' → s'.f = s.f` | every leaf of `a`'s body leaves `f` unchanged; a projection of `M.a.frame` |
| `M.a.mono_f` | `(RTS).tr th s (.a args) s' → ∀ x₁…xₖ, s.f x… = true → s'.f x… = true` | `f` has codomain `Bool`; every leaf leaves `f` unchanged or writes literal `true` at every pattern; at least one leaf writes |
| `M.f.mono` | `(RTS).tr th s l s' → ∀ x₁…xₖ, s.f x… = true → s'.f x… = true` | every action has `a.frame_f` or `a.mono_f` |
| `M.f.init` | `(RTS).init th s → ∀ x₁…xₖ, s.f x… = v` | the initializer writes `f` once, at the all-`none` pattern, with a closed value `v` (`false`, `0`, `none`, an enum constructor, …) |
| `M.a.tr_of_step` | `(RTS).tr th s (.a args) s' → ⟨body of a.ext.tr at th s s'⟩` | every imperative action: the exposed transition body, computed once by simplification and proven by `Eq.mp`; every lemma of `a` starts from it (§2.4) |

Per action and field, exactly one of `frame_f`/`mono_f` is emitted, or
neither. All binders except the transition hypothesis are implicit: a
consumer writes `M.a.frame_f h` or `M.f.mono h x hx`. Field equality in
`frame_f` is on the structure field itself (`s'.f = s.f`, a function
equality for relations), which rewrites under any `FieldRepresentation.get`
view a consumer may have wrapped it in; the pointwise form follows by
`congrFun`.

`M.f.init` is included because the contract fields the step facts feed come
in triples — monotone along transitions, frame for other actions, initially
absent — and its derivation is the same fragment applied to the
initializer's record. It is the one addition to the decided list; it is
cheap (one lemma per component) and drops the remaining hand-written
initial-state facts.

### 2.2 Derived, never assumed

Every emitted theorem is proven and kernel-checked at generation time. The
generator's decision procedure only chooses *what to attempt*; a wrong
decision produces a failed proof and no lemma, never a false lemma.

**Detection** (`MetaM`, on `(← getConstInfo (M.a.ext.tr)).value!` after a
`lambdaTelescope` over the parameters and `r₀ s₀ s₁`): collect the leaves
by structural recursion on `And`, `ite`/`dite` (both branches), `Exists`
(the body), and conjuncts that do not mention `s₁` (guards, dropped). A leaf
is `Eq _ (setIn (State.mk χ u₁ … uₙ) s₀) s₁` or `Eq _ s₀ s₁`. A
conjunct that mentions `s₁` and is neither → the whole action is
*unrecognised*: no lemma for any field of `a`, and `M.f.mono` is blocked
for every `f`. Per leaf and field position `i`, classify `uᵢ`:

* `unchanged` — `uᵢ` is `State.fᵢ (getFrom s₀)` (or the leaf is `s₀ = s₁`);
* `setTrue` — `uᵢ` is `FieldRepresentation.set d u'` with `u'` classified
  `unchanged` or `setTrue`, and `d` a `List` literal every element of which
  is `Prod.mk pat (fun x₁ … xₖ => Bool.true)` — the pattern is not
  inspected; a conditional whose other branch does not write `f` is
  covered because the branches are separate leaves;
* `setConst v` (initializer only) — as `setTrue` with a single element
  whose pattern is all `none` and whose body `v` is closed up to the
  module's parameters: no loose bound variables, no free variable outside
  the parameter telescope (so not `r₀`, `s₀`, `s₁`, not a `pick`ed value;
  a numeral qualifies although its `OfNat` instance names the sorts through
  the field's type);
* `other` — anything else: a `false` write, a value computed from the state
  (`f n := f n && g`), a value bound by `pick` or `:= *`, a `module`-kind
  component, a nested `set` of unknown shape.

`frame_f` ⇔ all leaves `unchanged`; `mono_f` ⇔ all leaves ∈
{`unchanged`, `setTrue`} and some leaf `setTrue`; `f.init` ⇔ the
initializer's leaf is `setConst v` at `f`. Anything else emits nothing for
`f` — including a `true` write in one branch and a `false` write in
another, and a bulk reassignment `f N := g N`.

**Proof** (a tactic script elaborated against the generated statement;
exact form fixed during implementation against a test module that has one
action per grammar production):

```
-- expose the body of this action in the transition hypothesis h
simp only [M.relationalTransitionSystem, M.Next, M.NextAct, M.a.ext.derived_eq, M.a.ext.tr] at h
-- walk the grammar to the leaves; every leaf substitutes the post-state
repeat' (first | casesm* _ ∧ _, ∃ _, _ | split_ifs at *)
all_goals (subst_vars; <close>)
```

where `<close>` is `rfl` for a frame (the projection of a `State.mk` under
`instIsSubStateOfRefl.setIn` is the pre-state field by iota/`rfl`), and for
a monotonicity or initial-value lemma the canonical-representation
evaluation already used by consumers and by `VeilTest/TrSimp.lean`'s
`marked_mono`, applied **to the goal only**:
`simp [FieldRepresentation.set, FieldRepresentation.get, CanonicalField.set,
FieldUpdateDescr.fieldUpdate, FieldUpdatePat.match, IteratedArrow.curry,
IteratedArrow.uncurry, IteratedProd.patCmp,
instIsSubStateOfRefl.setIn_overwrite, instIsSubStateOfRefl.getFrom_id,
Option.elim, hx]`, which reduces the pattern match (`if match then true
else old`) and closes with the hypothesis `hx`; `simp_all` with the same set
is the fallback. Goal-directed rather than `simp_all` first because
`simp_all` also rewrites every guard hypothesis with every other and did
not terminate within the heartbeat budget on an action with six
ghost-relation guards and nested `if`s (`VeilTest/Tactics/VeilExactState.lean`).
`M.f.mono` is `cases l` with one `case <action> =>` per label, closed by
that action's `mono_f` or by `frame_f` rewritten pointwise; `M.f.init` is
the same script on `initializer.ext.tr th default s`, its right-hand side
the literal re-bound to the lemma's binders by name (a numeral's `OfNat`
type argument is first reduced to `ℕ`, or `simp` cannot see through it at
instance transparency). All scripts were validated by hand on the
eight-shape module before being generated, and the full test suite found
the two failure shapes above.

Statement and proof are elaborated as *terms* (under `withoutErrToSorry`,
with the tactic block run inside it) and added with `addDecl`, not through
the `theorem` command: a failing tactic throws instead of being logged and
admitted, so no `sorry`-backed lemma and no stray error can reach the
user's file. Any exception during detection, statement elaboration or proof
of one lemma is caught per lemma; whatever the failed attempt logged is
dropped, the lemma is skipped and — only when detection said yes and the
proof failed — named in a warning, because that combination is a bug in the
script, not a property of the model.

### 2.3 Where, when, and how loudly

* **Site**: a new file `Veil/Frontend/DSL/Module/StepLemmas.lean`,
  called once from `Module.ensureSpecIsFinalized`
  (`Module/Elaborators.lean`) after `assembleRelationalTransitionSystem`
  and before `Verifier.runManager`, inside the existing
  `unless (← isModelCheckCompileMode)`. One call site in the merge-hotspot
  file; everything else in the new file. Names in `Module/Names.lean`.
* **Statements as syntax**: the binder regime is the RTS's own
  (`sortBinders ++ inhabitedBinders ++ userDefinedBinders`, as
  `assembleRelationalTransitionSystem` builds it, with the sorts and user
  parameters made implicit), the label is `M.Label.a args` with `args`
  from `declarationAllParams`, and statement and proof are elaborated as
  terms and added with `addDecl` (§2.2). This uses only upstream APIs; it
  does not need `withCanonicalRTS` (Part II does). The lemma's own binders
  (`veil_th`, `veil_s`, `veil_s'`, `veil_l`, `veil_h`, `veil_x0 …`) carry a
  `veil_` prefix so that they cannot capture an action argument named `s`
  or `th`; **not** the `__veil_` prefix of the elaborator's
  implementation-detail identifiers, because `LocalDeclKind.ofBinderName`
  classifies a `__`-prefixed binder as an implementation detail and
  `subst_vars` skips such hypotheses — the post-state equation would then
  never be substituted (found on the initializer path, where `simp only`
  does not replace the hypothesis by a fresh one).
* **Option**: `veil.gen.stepLemmas : Bool`, default `true`, registered in
  `Veil/Base.lean` next to `veil.gen.modelCheckScaffolding`; when `false`
  nothing is emitted. The default is provisional until the measurement in
  §2.4.
* **Silence**: emission produces **no message** on success. Every
  `VeilTest` file that pins `#gen_spec` with `#guard_msgs` expects no
  output, and an info line here would break them all for no benefit. The
  per-field verdicts, counts and timing go to `trace.veil.stepLemmas` and
  to a `veil.perf.elaborator.stepLemmas` profiler node. A proof failure
  after positive detection is a `logWarning` naming the lemma (§2.2).
* **`veil.noVerify`**: emission is solver-free and kernel-checked, so it
  runs; if the measured cost matters for editor sessions, gate it on the
  option only, which the user controls.

### 2.4 Cost, and the measurement that fixes the default

Per lemma: one `simp only` over three definitions, one over two, a handful
of `obtain`/`split_ifs`, and `rfl` or one `simp` — milliseconds each. The
largest downstream module has 40 actions and 29 mutable components: about
1 100 frame candidates, a few dozen monotonicity lemmas, up to 29 `init`
and `mono` lemmas — estimated seconds and megabytes of olean, against a
measured 127 s build for that module before this change.

**Measured** (validation worktree, the 40-action / 29-component module,
`LEAN_NUM_THREADS=8`, two timed builds per configuration after a warm-up;
1056 frame, 38 monotonicity, 24 whole-system monotonicity and 29
initial-value lemmas are derived, every action recognised):

| Generator | build, option on | emission | vs. option off (121–123 s) |
|---|---|---|---|
| one `simp only` and one destructuring proof per field lemma | 144 / 144 s | 18.2 s | +22 s (18 %) |
| + per-action exposure lemma `M.a.tr_of_step` | 136 / 137 s | 14.5 s | +15 s |
| + per-action frame bundle `M.a.frame`, fields as projections | 131 / 132 s | 10.6 s | +9 s |
| + one binder scope per action (exposure, bundle, projections) | 127 / 127 s | 7.7 s | +5 s (4 %) |

So the shape that ships is: per action, **one** elaboration of the fifteen
binders, inside which the exposure lemma is computed by an `Expr`-level
simp of the hypothesis type (`Eq.mp` of the simp proof), the frame bundle
`s'.f₁ = s.f₁ ∧ … ∧ s'.fₖ = s.fₖ` is the one tactic proof
(`replace h := M.a.tr_of_step h; <destruct>; all_goals (subst_vars; exact ⟨rfl, …⟩)`),
and every `M.a.frame_f` is an `And` projection of it (no tactic, trivial
kernel check). Monotonicity, whole-system monotonicity and initial-value
lemmas keep their own small scripts (they are few). With this the default
stays `true`; the 7-action module's build is unchanged within noise
(34–38 s). The two earlier shapes are recorded because each was a factor of
about 1.3 by itself and neither alone would have justified the default.

### 2.5 Deliberately not derived, and possible extensions

Not derived, by design: non-literal writes, `false` writes, bulk
reassignments to a non-literal, `function` and non-`Bool` `individual`
monotonicity, `module`-kind components, and every field of an
*unrecognised* action. `transition`-syntax actions are unrecognised, so a
module containing one gets per-action lemmas for its imperative actions
only and no `M.f.mono`. Whole-system frames (`M.f.frame`, a field no action
writes) are not emitted: such a field is a modelling smell, and the
per-action lemmas already cover it.

Three extensions use the same detection and proof machinery and are
candidates for a follow-up commit on the same branch once the core is
measured; they are **not** in the initial scope unless accepted at review:

* **Effect**: `M.a.effect_f : tr … → ∀ x…, x₁ = t₁ → … → s'.f x… = v` for
  a single-element `set` at a pattern whose `some` positions are
  action-argument terms `tᵢ` and a closed value `v`.
* **Pointwise frame**: `M.a.frame_f_at : tr … → ∀ x…, (¬ pattern matches x) → s'.f x… = s.f x…`
  for the same fragment — together with the effect lemma this is the full
  characterisation of a single write.
* **`transition` frames**: the `[unchanged| f = f']` conjuncts of a
  `transition`-syntax action are positional and known at elaboration time
  (`elabTransition` computes `unchangedFields`); `frame_f` for them is one
  projection out of `of_decide_eq_true`.

The first two would retire the last record-derived hand proofs downstream
(an action's effect at its own indices and its frame at other indices);
without them those two theorems stay hand-written one-liners.

### 2.6 Tests and validation

`VeilTest/StepLemmas.lean`: a module with one action per grammar production
(plain `true` write, conditional without `else`, conditional with a
different write in `else`, `pick`, bulk `true`, `false` write, shallow
`&&` write, write through a procedure) and a `transition`. Pins:
`#print axioms` on a frame, a per-action monotonicity, a whole-system
monotonicity and an `init` lemma (standard axioms only); `#check` failures
pinned for the lemmas that must *not* exist (`mono_f` for the `false`
writer; `M.f.mono` blocked by it; nothing for the `transition`); a
consumer `example` using `M.f.mono` and `M.a.frame_f` with no hand
unfolding; the option off → no lemma; `#guard_msgs in #gen_spec` stays
silent. Full `lake build VeilTest`.

Downstream validation, in the validation worktree re-pinned to the branch:
the two `StepFacts` sections become one-line applications of the generated
lemmas (or are deleted where a consumer can use the generated name
directly), both instance files and the audit root build, and the build time
of the 40-action module is measured with the option on and off (§2.4).

### 2.7 Branch and dependencies

`port/step-lemmas`. Expected base `be6a1cee` (`upstream/main`): the
generator reads upstream definitions and adds one call in
`ensureSpecIsFinalized`. If the proof script uses the `trSimp` attribute
rather than naming `derived_eq`/`tr` per action, the base is
`port/hygiene-bundle` (`7f9fd9f8`). Measured by trial cherry-pick with
`merge-tree` before cutting, as for the previous items.

## 3. Part II — `step_property`

### 3.1 The class, and its boundary

A `step_property` `P` is checked as an **action property**: for every
action `a`, `Assumptions th → Invariants th s → (a.ext.tr … th s s') → P th s s'`
— TLA⁺'s `□[P]_v` under the inductive invariant. This is strictly more than
an invariant (which speaks about `s'` alone) and strictly less than general
safety: a property relating non-adjacent states — "no `open(s)` after a
`complete(s)`", "every finalised value was proposed earlier" — needs
history state, which is Part III. Every step-level field of the downstream
contracts is in this class (a monotonicity, a frame under a guard, an
effect), so the form maps one-to-one onto what contracts consume; it is not
a stopgap for Part III.

### 3.2 Syntax and elaboration

```lean
step_property [opened_mono] { opened I S → opened' I S }
step_property [committed_frozen] { local_committed I → local_committed_pos' I J M → local_committed_pos I J M }
```

* `step_property (propertyName)? "{" term "}"`, a new scoped keyword in
  `Module/Syntax.lean`. The braces mirror `transition`, the other form with
  primed fields, and visually separate two-state bodies from one-state
  properties. Default name `step_<n>`.
* The body uses the primed-field notation of `transition` bodies: `f` is
  the pre-state component, `f'` the post-state one. Capitalised variables
  are universally quantified, as in `invariant`. Only mutable components
  have a primed form; a primed immutable is rejected before elaboration,
  at the identifier, with a message saying the component is immutable and
  has no post-state (the L13 pattern; detection as `elabTransition`'s
  `changedFn`).
* Elaboration: a two-state variant of `withTheoryAndState`
  (`Module/Util/Assertions.lean`) built on `withTheoryAndStateTermTemplate`
  with the targets `[(.theory, th), (.state none "_conc", st), (.state "'" "_conc'", st')]`
  — the `transition` case's binding, with hygienic
  (`mkVeilImplementationDetailIdent`) binders. The definition is
  `M.<prop> : {params} → [Decidable …] → ρ → σ → σ → Prop`, `abbrev`,
  tagged `invSimp`/`nextSimp` like invariants, with no `by veil_exact_*`
  default arguments (those exist so invariants can be applied inside action
  bodies; a step property is never applied there).
* Representation: `StateAssertionKind.stepProperty`
  (`Module/Representation.lean`), with the six existing match sites
  extended (default name, kind string, trace string,
  `declarationBaseParams → mod.parameters`, the `LocalRProp` filter → no
  locality instance, `#model_check`'s filters → ignored). `Module.stepProperties`
  next to `checkableInvariants`; **not** in `Module.invariants`, so
  `Invariants`, `Safeties`, the preservation lemmas and `#gen_composition`
  are untouched.

### 3.3 Semantics: one cell per action

A new specification form in `Action/Semantics/Definitions.lean`:

```lean
@[reducible] def Transition.meetsStepSpecificationAssuming
    (act : Transition ρ σ) (assu : ρ → Prop) (pre : SProp ρ σ) (P : ρ → σ → σ → Prop) : Prop :=
  ∀ r₀ s₀ s₁, (assu r₀ ∧ pre r₀ s₀) → act r₀ s₀ s₁ → P r₀ s₀ s₁
```

and its trivial bridge `Transition.step_of_meets` (the two-state analogue of
`Transition.triple_of_meets`). `Module.generateStepPropertyVCs`
(`VCGen/Induction.lean`, called from `ensureSpecIsFinalized` next to
`generateInvariantVCs`) adds, for every action `a` × step property `P`, one
primary VC named `a_P` with property `P`, built by the existing
`mkVCForSpecTheorem` with this spec form, `act.ext.tr` as the transition,
`Assumptions` and `Invariants` as the hypotheses, and `@P args` as the extra
term. Decisions:

* **Hypotheses**: the module's assumptions and its full invariant
  conjunction at the pre-state, like an induction cell. Step properties are
  **conclusions only**: no cell assumes another step property. (Allowing it
  would need an order to stay non-circular; nothing downstream needs it.)
* **No initializer cell**: `Init` has no meaningful pre-state.
* **No WP alternative**: the two-state postcondition has no
  `VeilM.meetsSpecificationIfSuccessfulAssuming` encoding; a step cell has a
  single, TR-style entry. (A WP encoding — `wp act (fun _ r s' => P r₀ s₀ s') r₀ s₀`
  under an outer `∀ r₀ s₀` — exists and could later fill the
  alternative slot; not now.)
* **Retries** as for every cell (`veil.smt.retries`).

### 3.4 Discharge

A new tactic `veil_solve_step := veil_intros; __veil_solve_tr_conservative`.
The TR pipeline already handles two-state goals: `veil_intros` introduces
`th st s₁ ⟨has, hinv⟩` and the transition hypothesis; the conservative route
unfolds `Invariants`, `actSimp` (which includes the `reducible` `tr`) and
the step property, splits conditionals, and `veil_concretize_tr` turns the
`setIn … = s₁` equation into explicit pre- and post-state fields
(`setIn_makeExplicit`, then field equalities viewed through `get`), which
is exactly what a `P th s s'` conclusion needs. `veil_solve_tr` itself is
not reused because its fast path, `veil_apply_local_tr`, pattern-matches
the one-state spec form and can only fail before falling back; a
step-specific local bridge (the two-state analogue of
`defineTransitionMeetsSpecificationIfSuccessfulAssumingLocalTheorem`) is
the mitigation if the conservative route turns out slow at scale — its cost
on a 60-invariant module is the one unmeasured risk in Part II.
Counterexamples: the TR path's two-state models are rendered by the
existing induction renderer, which does not inspect the VC style.

### 3.5 Plumbing

* **Registry**: `VCStyle.step` (`Infra/Metadata.lean`), JSON `"step"`,
  discharger suffix `_STEP`, `VCRegistryEntry.dischargeTactic → veil_solve_step`.
  The three `VCStyle` consumers are `dischargeTactic`, `nameSuffix` and the
  registry entry. A third constructor rather than a new field, because the
  style's documented role is "determines the statement form and the
  discharge tactic", and that is exactly what differs.
* **Sweep report**: step cells are listed under their action with the
  invariant cells (`formatVerificationResults` groups by action). When the
  results contain a `.step` cell the header reads "…must preserve the
  invariant, satisfy the step properties, and successfully terminate:";
  otherwise the text is unchanged, so no existing pin moves.
* **`#check_action`, `#check_vc`, `#prove_action`, `#prove_vc`**: filter by
  action/property metadata and read the tactic from the registry entry —
  nothing to add beyond the style.
* **`#gen_theorems`** persists proven step cells as `M.a_P` like any cell.
* **`#veil_status`** counts registry cells by (action, property) and
  resolves `a_P` — step cells are counted with no change; the test pins the
  new total.
* **Model checker and traces**: unaffected; `#model_check` does not check
  step properties in this iteration (they are not in `Invariants`).

### 3.6 Composition exports

With every `a_P` cell theorem present, the whole-system form is one `cases`
over the label:

```lean
theorem <ns>.P_step {binders} {th s s' l} (hassu : (RTS).assumptions th)
    (hinv : Invariants th s) (htr : (RTS).tr th s l s') : P th s s'
```

emitted by `emitStepLemmas` in `Module/Composition.lean`, at the canonical
instantiation (`withCanonicalRTS`), each case closed by the action's cell
theorem through `derived_eq` and `Transition.step_of_meets` — the regime of
the L14 preservation lemmas. Called by `#gen_theorems` (in-file; a second
summary line only when the module has step properties) and by
`#gen_composition` (file family), idempotent like `emitPreservationLemmaCore`.
`#gen_composition` additionally emits `reachable_P_step :
reachable th s → (RTS).tr th s l s' → P th s s'` by composing with
`invariants_of_reachable` — the form a contract instance consumes directly.
The name `P_step` avoids both L14's `step_<action>` and the cell names
`<action>_<property>`.

### 3.7 Not included

`trusted step_property` (assumed, unchecked); step properties as
hypotheses of other cells; a WP encoding; model-checker support; a
step-specific local bridge (only if measurement demands it).

### 3.8 Tests and validation

`VeilTest/StepProperty.lean`: a module with a monotone relation, a
counter, and a flag; `step_property`s that hold (`r N → r' N`; a frozen
relation under a guard, which needs the guard; one that needs an
invariant), and one that fails on one action (pinned ❌; see §3.9 on the
counterexample); the sweep report with the
new header wording; a primed immutable rejected; `#gen_theorems` +
`#print axioms` on a cell and on `P_step`; `#veil_status` total.
`VeilTest/StepPropertyBase.lean` + `VeilTest/StepPropertyRegistry.lean`: the
registry round trip — `#check_action M a` and `#prove_action M a` cross-file
on step cells, `#gen_composition` emitting `P_step`/`reachable_P_step`.
Pins use `(drop info)`/`(whitespace := lax)` where the recipe requires.
Full `lake build VeilTest`.

Downstream validation, in the validation worktree: the step-level contract
fields are proven from `step_property` cells stated in the two models —
including the two that Part I cannot derive (a relation frozen once a flag
is set; the paper's monotonicity, which needs an invariant of the
pre-state) — both models re-solve green with the new cells, and
`#veil_status` counts them.

### 3.9 Implementation notes

What was built follows §3.2–§3.6; the points below are where the code is
more specific than the design, or departs from it.

* **Elaboration.** The body is elaborated by a two-state variant of the
  assertion machinery (`withTheoryAndTwoStates` in `Util/Assertions.lean`):
  three targets — the theory, the pre-state, and the post-state whose
  components are bound under their primed names — and binders
  `(th : ρ) (st : σ) (st' : σ)`, so the property's type is `ρ → σ → σ → Prop`
  over the module's usual parameter telescope. `defineAssertion` selects it
  by kind. A step property is *not* a local reader-proposition
  (`isStateAssertionWithState … = false`): it is not part of `Invariants`,
  not in the invariant clumps, and not seen by the model checker or the
  trace commands, exactly as §3.5 intends.
* **Primed immutables** are rejected syntactically at the elaborator
  (`throwIfStepPropertyPrimesImmutable`), before the term is elaborated, with
  the message anchored at the offending identifier — the two-state
  elaboration would otherwise fail on an unbound name far from the cause.
* **Cells.** `mkStepPropertyVC` (`VCGen/Induction.lean`) is a thin wrapper
  over the existing `mkVCForSpecTheorem` with the two-state spec form, the
  `.step` style and the `<action>_<property>` name; `generateStepPropertyVCs`
  is called from `ensureSpecIsFinalized` right after `generateInvariantVCs`
  (and from `generateVCs`), one primary VC per action × property with the
  `_STEP` discharger and the usual retry ladder. `actionIdent` resolves
  `.step` like `.tr` (the pre-computed `ext.tr`).
* **Exports.** `emitStepLemmaCore` (`Module/Composition.lean`) instantiates
  the property constant at the canonical spine by *binder name*, through a
  `byName` map now carried by `CanonicalRTS` (the same map that instantiates
  `Invariants`). The exported statement therefore shows `Invariants` at the
  module's own instantiation — its four explicit parameters (reader, state,
  sorts, representation family) — where §3.6 wrote the schematic
  `Invariants th s`; the RTS telescope (sorts implicit, `Inhabited` and
  protocol classes explicit) is the binder regime, and `th s s' l` are
  implicit on both `<P>_step` and `reachable_<P>_step`. The per-action cell
  theorem is located through the file-family layouts (`ns`, `ns.Proofs`,
  `M.Proofs`, `M`) by `resolveCellTheorem`. Cross-file, the property names
  come from the registry's `.step` entries (`stepPropertiesOf`); inside the
  defining module, from the module state.
* **`transition`-syntax actions** have no `derived_eq`, so a module
  containing one gets its step *cells* (checked as usual) but no
  `<P>_step` export: `emitStepLemmaCore` reports which action blocks it.
  Same limitation, same reason, as the L14 preservation lemmas.
* **Reporting.** `#gen_theorems` prints its step-lemma summary line only
  when the module has step properties; `#gen_composition` appends a count of
  step exports to its single info line. The sweep header changes wording only
  when a `.step` cell is present, so no existing pin moved.
* **Tests** as in §3.8, with two pinning deviations: the refuted cell is
  pinned with counterexample printing off (the model text is not stable
  enough to pin), and the `#gen_theorems` / `#gen_composition` /
  `#prove_action` summaries are unpinned because they carry timings. The
  consumer example is written against `reachable_<P>_step`, whose hypotheses
  need no module instances; stating the conclusion by hand outside the module
  would require the canonical representation instances, which the regime
  passes explicitly.
* **Discharge** is as designed (`veil_solve_step`); the step-specific local
  bridge of §3.4 was not needed — every step cell in the tests and in the
  downstream validation closes on the conservative route.

### 3.10 Branch and dependencies

`port/step-properties`, on `port/composition` (`55d7518c`), which contains
`port/vc-registry` (the `VCStyle` field of the registry entry and the
cross-file commands) and the composition machinery (`withCanonicalRTS`,
`#gen_theorems`' emission hook, `#veil_status`). Independent of Part I in
code; the two leaves merge into `port/integration` after both reports.
Measured before cutting.

## 4. Part III — auxiliary (history) components: the declared next step

Not for this work. The proposal, recorded so Parts I and II stay compatible
with it: a state-component modifier (the `immutable` machinery is the
template) marking a component *auxiliary*. Auxiliaries may be assigned in
actions and the initializer and read by assertions — including
`step_property` bodies, both `f` and `f'` — and by other auxiliaries'
updates; the elaborator rejects them in `require`s, branch and `pick`
conditions, right-hand sides of real components' updates, `transition`
constraints on real fields, and assumptions. Erasure is then a refinement
by construction, justified first by a documented meta-argument and later by
a generated projection-simulation theorem; the system-versus-proof-artifact
split of a model becomes visible in the source.

Compatibility constraints this note commits to:

* Part II's body elaborator resolves fields through
  `withTheoryAndStateTermTemplate`, which exposes every mutable component;
  an auxiliary is a mutable component with an extra flag on
  `StateComponent`, so it is readable in step-property bodies with no
  change to Part II. The erasability rules live on the *action* side.
* Part I treats auxiliaries as ordinary state fields, so the history
  relation of a model gets its `frame`/`mono`/`init` lemmas for free —
  which is what history-variable arguments consume.
* Neither part introduces a keyword or a semantics that a later `ghost`-like
  component modifier would collide with; the upstream scratchpad work on
  this is to be read only when Part III is designed.

## 5. Decisions requested at review

1. **`M.f.init`** in Part I's initial scope (recommended: yes; §2.1).
2. **Effect and pointwise-frame lemmas** (§2.5): follow-up commit on the
   same branch after the cost measurement, or not at all.
3. **`veil.gen.stepLemmas` default `true`**, to be confirmed by the
   measurement in §2.4; the bundled-frame fallback if per-field cost hurts.
4. **`step_property [name] { … }`** with braces (as decided) — confirm.
5. **`VCStyle.step`** rather than a new registry field (§3.5).
6. **Names**: `M.a.frame_f`, `M.a.mono_f`, `M.f.mono`, `M.f.init`;
   `P_step`, `reachable_P_step`; tactic `veil_solve_step`; option
   `veil.gen.stepLemmas`.
7. **Silent emission** in Part I (no info line at `#gen_spec`; trace class
   and a warning only on a positive-detection proof failure).
