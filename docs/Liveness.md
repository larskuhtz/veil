# Deductive liveness for Veil — ω-acceptance via liveness-to-safety

*Design proposal, not implemented. This document is the Veil-side home for
liveness work: what surface syntax the tool should grow, and how the
obligations are discharged with the machinery Veil already has. It was moved
here (2026-08-25) from the Cadence verification project
([`larskuhtz/cadence`](https://github.com/larskuhtz/cadence)), which keeps
the consumer-side half — which of its liveness obligations are already
machine-checked as fair-progress invariants, which named fairness
assumptions remain, and what this extension would reduce them to — in its
`docs/Liveness.md`.*

The proposal is deliberately narrower than full LTL: most
distributed-systems liveness obligations are naturally expressible as
ω-acceptance conditions on a labelled transition system (LTS), and can be
discharged by a **liveness-to-safety (L2S)** reduction that reuses the
existing safety-VC machinery.

## 1. Why Veil's structure already does most of the work

A `veil module` already produces a **labelled guarded transition
system**: every action has a distinct name (the label), an explicit
guard (`require` clauses) and an explicit update. No control-flow
analysis is needed to recover an LTS — it is already first-class.

That is the structural prerequisite for everything below.

## 2. Surface syntax — ω-acceptance, not LTL

Rather than introducing an LTL parser, the proposed extension exposes
ω-conditions directly. Two cases cover the vast majority of practical
properties:

* **Buchi-style "infinitely often"** — assert that some action label
  fires infinitely often, or that some state predicate holds
  infinitely often.
* **Response / leads-to** — `p ↝ q` (`p` eventually implies `q`),
  i.e. `□ (p → ◇ q)`. This is the most common shape in distributed-
  systems work and subsumes "eventually `q`" via `p ≡ true`.

A strawman surface syntax:

```
fairness justice    send_vote                -- weak-fair action
fairness compassion deliver                  -- strong-fair action

acceptance [block_progresses]
  infinitely_often  finalize_commit          -- Buchi acceptance

response [eventual_commit]
  ¬ is_byz i ∧ voted i s    ↝    committed i s
```

LTL operators beyond `□`, `◇`, `↝`, and `infinitely_often` are
deferred. They are convenient but not load-bearing for the kinds of
properties Cadence-style protocols generate. Even a *block-counter
monotonically advances* property is naturally captured as "the action
that increments the counter fires infinitely often, and each occurrence
strictly changes the counter".

## 3. Discharge via liveness-to-safety (L2S)

The proposed reduction is the one developed for first-order
transition systems by Padon, Hoenicke, Losa, Podelski, Sagiv, Shoham
(*Reducing Liveness to Safety in First-Order Logic*, POPL'18). The
construction in two sentences:

> Augment the state with (a) a *witness snapshot* `σ̂` of a candidate
> "lasso head" state and (b) a flag per fairness obligation tracking
> whether that obligation was discharged since the snapshot. The
> negation of the ω-property becomes a *safety* property of the
> augmented system: it is unsafe ever to return to `σ̂` with the
> property still false and all fairness obligations satisfied (i.e.
> with a fair lasso closed).

The crucial property for Veil: the resulting verification obligation
is a **standard inductive-invariant problem on an augmented state
space**. Every piece of existing Veil machinery (`#gen_state`,
`#gen_spec`, the per-action induction VCs, the SMT discharge
pipeline, the auxiliary-invariant patterns exercised by
`Examples/Ivy/ReliableBroadcast.lean` and, at scale, by the Cadence
project's Chorus model) applies verbatim. No new SMT theory for
well-founded orders is required; no new tactic family is required. The
user authors *auxiliary invariants for the augmented system* — a skill
they already exercise for safety.

## 4. Meta-theoretic assumptions

The L2S reduction is sound *modulo* the fair-scheduling assumption:
every action declared `justice` (resp. `compassion`) is assumed to
fire whenever continuously (resp. infinitely-often) enabled. These
assumptions belong in the framework's meta-theory and should be
documented prominently:

* They are **scheduling** assumptions about *honest* actions — a
  consumer model's Byzantine-adversary actions (e.g. the `byz_*`
  family in Cadence's Chorus model) carry no fairness annotation and
  are *not* subject to them.
* They are **distinct from** network-level eventual-delivery
  assumptions. Byzantine-consensus liveness needs *both* a
  fair-scheduling assumption on the validator's local actions *and* a
  network-level delivery assumption. The latter is most naturally
  expressed as a separate compassion annotation on a synthetic
  `network_deliver` action — or, in an explicit-network model, as
  compassion on its delivery action.

## 5. Ranking functions — keep as an option, not a requirement

The STeP / verification-diagrams style (annotate response properties
with a ranking function into a well-founded order) is more *readable*
than L2S in cases where the ranking is obvious — "the queue size
strictly decreases", "the round number strictly increases". For these
cases the SMT obligations are simple (linear arithmetic on `ℕ`),
which Z3 handles cleanly.

It would be a worthwhile *second-tier* feature: a `ranking λ st => …`
annotation on `response` properties, generating a per-helpful-action
VC that the rank strictly decreases (or `q` is established directly).
But it is not the recommended primary path because:

* It introduces a new VC shape (well-founded decrease) that the
  user must reason about separately from inductive invariants.
* L2S already handles the same set of properties.
* For complex properties where the ranking is non-trivial
  (e.g. lexicographic over multiple counters), L2S auxiliary
  invariants are usually no harder to author.

A reasonable rollout order: L2S first (covers everything), ranking
mode later (ergonomics for the common easy cases).

## 6. What stays out of scope

* **Real-time / time-bounded liveness.** Bounded-delivery, eventual
  synchrony with a *finite* GST, deadlock detection under
  partial-synchrony — all require a notion of clock and reasoning
  about elapsed steps. Encodable in the framework (clocks are just
  monotone variables) but requires user discipline; the verifier
  itself does not need new theory.
* **Probabilistic liveness.** Asynchronous Byzantine agreement of
  the Ben-Or / common-coin / MVBA family terminates with probability
  1, not deterministically. No deductive FOL framework — STeP-style
  or L2S — handles probabilities. The standard move is to model the
  randomised primitive as an *axiomatic black box* with a
  deterministic termination guarantee assumed under a fair-scheduling
  precondition; the probability-1 argument lives on paper.
* **Full LTL** (next-step `X`, until `U` other than the response
  shape, past-time operators). Useful for some hardware-verification
  properties; rarely needed in distributed-systems work; can be
  added later via a Buchi-product translator on top of L2S.

## 7. Concrete bring-up plan

Sketching what a first implementation might look like:

1. **Action labels are already there** (`procedure_definition` /
   `action_definition` carries a name). Expose them in the model
   metadata so future syntax can refer to them.
2. **Add fairness annotations**: `fairness justice <name>`,
   `fairness compassion <name>`. Store as part of the module's
   metadata; surface them in the L2S construction below.
3. **Add `response p ↝ q`** as a top-level declaration that desugars
   to:
   a. Synthesised auxiliary state: `witness_p : state`,
      `witness_active : Bool`, and per-fair-action `fired_since_snap`
      flags.
   b. Generated transition relation that, on entering a `p ∧ ¬q`
      state, may non-deterministically snapshot.
   c. Generated safety property: it is unsafe to be back at
      `witness_p` with `witness_active`, every `fired_since_snap`
      true, and `q` still false.
   d. Hand off to the standard `#check_invariants` pipeline.
4. **Add `acceptance infinitely_often <action>`** as a degenerate
   case of (3): `p = true`, `q` defined by the action's firing flag,
   reduces to "the firing flag is set infinitely often".
5. **Document the fair-scheduling assumption** as a load-bearing
   meta-theoretic claim of the framework (analogous to the
   monotone-network (M-update)+(M-frame) contract the Cadence project
   documents for its models).
6. **Optionally** layer a ranking-function shorthand for
   easy-ranking response properties on top of (3).

Steps 1–5 are SMT-discharge-only and reuse the existing pipeline;
step 6 is an ergonomic extension.

## 8. First consumer

The Cadence verification project is the intended first consumer and the
measure of "done": its liveness argument is already factored so that the
machine-checked part (fair-progress invariants) and the assumed part
(named fairness and oracle-termination axioms) meet exactly at the seam
this extension would close. Its `docs/Liveness.md` states which of its
obligations become dischargeable at each step of §7, and which stay out
of scope for the reasons in §6.
