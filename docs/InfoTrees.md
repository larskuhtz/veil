# Info trees of Veil's declarations

Veil's declaration commands (`after_init`, `action`, `procedure`,
`transition`, the assertions and `step_property`) keep only a slim form of
their info trees (`withSlimVeilInfoTrees` in `Veil/Util/Meta.lean`), and
`#gen_spec` records none. This note says why, what is kept, and what was
measured.

## The problem

Lean's frontend keeps every command's info tree alive until the end of the
file. The command line does this so it can write the `.ilean`, and the
language server for as long as the file is open. An info tree node holds its
local context, and the context node above it holds the metavariable context
of the elaboration that produced it.

A Veil declaration elaborates far more than the user wrote: the action's
derived definitions, its weakest-precondition forms, its lemmas. All of that
is positioned on the user's syntax, and all of it was recorded. On a large
model the retained trees, with the contexts they point to, grew the memory
steadily over the whole file.

The model this was measured on is Cadence's `Chorus`: 46 actions, 101
properties and 9 587 VCs. Its memory grew by about 6 GB over the file, against
a 136 MB olean. `#gen_spec` added a further 4–5 GB while it ran. On a 4-core
CI runner with a 13 GB container, that made the model's build an intermittent
out-of-memory kill.

## What is kept

The wrapper runs the elaborator, then replaces its info trees with one
`TermInfo` per reference at an original source position: the identifiers the
user wrote, including the definition site that `addVeilDefinitionSiteInfo`
records. Each reference keeps its enclosing-declaration context
(`parentDeclCtx`), which the `.ilean` records.

- A constant keeps no context at all.
- A local variable (an action's parameter, or a state component inside an
  action body) keeps the minimal local context its hover needs: its own
  declaration and, transitively, the declarations its type mentions. Types
  are instantiated, and no metavariable context is kept.

Kept:
- hover, go-to-definition and find-references on every identifier the user
  wrote;
- the `.ilean`. On `Chorus` it is identical to the one written without the
  wrapper: 242 referenced names, 207 definitions, 432 usage ranges, every
  usage and every enclosing declaration.

Dropped:
- hovers on the types of compound subterms;
- all info for generated syntax, which has synthetic positions.

`#gen_spec` has no user syntax, so it records nothing. Slimming it at the end
of the command would not help: the full tree would still exist until then,
and that is the peak.

## Measured

Setup: `lake build Cadence.Chorus` on Cadence at `LEAN_NUM_THREADS=4`, peak
resident set of the model's `lean` process, macOS, 14 cores, 36 GB. Run-to-run
noise is about ±1 GB.

The hover counts come from the rendered Chorus page of Cadence's Verso
literate site: `var` and `const` tokens that carry a hover.

| Veil | peak | memory after the first 2½ min | `.ilean` usage ranges | `var` / `const` hovers |
|---|---|---|---|---|
| without the change | 10.3 GB | climbs to the end | 432 | 2 585 / 577 |
| info trees off for these commands (rejected) | 7.7 GB | flat at 4.7 GB | 50 | — |
| constants only (rejected) | 8.6 GB | flat at 4.8–5.3 GB | 432 | 293 / 582 |
| constants and variables (this change) | 8.6 GB | flat at 4.8–5.2 GB | 432, identical | 2 602 / 582 |

The rise in the last ~50 s of every run is the VC registry and the olean
write, and it is unchanged. Keeping the variables' minimal contexts costs no
measurable memory.

On the change, the whole Cadence suite re-validated warm in 365 s. The two
single runs before it, on the earlier pins, took 631 s and 645 s on the same
machine; that is one run each, not a controlled comparison. Rendering the
Chorus page takes 377 s at a 6.0 GB peak.

The two rejected rows are the experiments that led here:
- switching info trees off loses every reference inside action bodies and
  properties;
- keeping constants only loses the hovers on an action's parameters and on
  the state components it reads.

A bisection on a scratch copy, with info trees switched off by region, found
the two sources:
- the declarations, whose trees grow memory steadily;
- `#gen_spec`, which adds 4–5 GB at the end.

Only switching off both brings the curve flat.
