# The VC registry: one elaboration run per statement

`port/registry-memory`, stacked on `port/vc-registry` (which introduced
`Module.persistVCRegistry`, in `Veil/Frontend/DSL/Module/VCGen/Induction.lean`).

## The problem

With `veil.gen.vcRegistry`, `#gen_spec` elaborates the closed statement of
every induction VC and persists it. The elaborations are split into
`getNumCores − 1` chunks, all started at once. Until this change each chunk
was **one** `liftTermElabM` run over all its statements, which had two
consequences, both proportional to the chunk size, i.e. to the VC count
divided by the machine's core count:

* **memory**: the run's elaboration state (metavariable context, caches)
  grew over the whole chunk. On a 4-core machine a module with 9 587 VCs
  (Cadence's Chorus model) had 3 chunks of ~3 200 statements alive at once,
  and its build was killed for memory in a 13 GB CI container;
* **heartbeats**: the chunk had one `maxHeartbeats` budget, taken when the
  run started on the worker thread, and the thread's heartbeat counter also
  advances for whatever other tasks the thread runs while the chunk waits.
  With fewer threads than chunks a queued chunk inherited that charge: the
  same module failed at `LEAN_NUM_THREADS=2` with "VC registry …: statement
  elaboration failed: (deterministic) timeout at `isDefEq`, maximum number
  of heartbeats (500000)", locally and on CI.

## The change

* Every statement is elaborated in **its own** `liftTermElabM` run, and the
  result is instantiated before the run ends. The live elaboration state is
  one statement per worker, and each statement has the budget and the
  heartbeat baseline of one command.
* The stored types are **hash-consed** (`Lean.ShareCommon.shareCommon` over
  the whole array) before the extension write, so the subterms all
  statements repeat (the invariant clump above all) are shared in memory, as
  the olean's compaction already shares them on disk.

No entry changes: each statement is the same `Expr`, only built in a fresh
state and then shared. Downstream, every cache key and every
`#veil_status` count stays (Cadence: the proof families replay warm after
the re-pin).

## Measured

Cadence's Chorus model (`lake build Cadence.Chorus`, model olean deleted,
macOS peak resident set, 14 cores / 36 GB; run-to-run noise about ±1 GB):

| model | Veil | `LEAN_NUM_THREADS` | result | peak | wall |
|---|---|---|---|---|---|
| Cadence master `8b13627` | before | 4 | ok | 17.7 GB | 302 s |
| Cadence master `8b13627` | **after** | 4 | ok | **15.6 GB** | 312 s |
| Cadence R8 (#54) | before | 4 | ok | 18.3 GB | 306 s |
| Cadence R8 (#54) | before | 2 | **registry heartbeat timeout** | 15.8 GB | 294 s |
| Cadence R8 (#54) | **after** | 2 | ok | **15.6 GB** | 355 s |
| Cadence R8 (#54) | **after** | 4 | ok | **16.7 GB** | 339 s |
| Cadence R8 (#54) | **after** | 8 | ok | **16.1 GB** | 324 s |

On this machine the old chunks were small (13 chunks of ~740, at most 4 or
8 in flight), so the saving here, 1.6–2.1 GB, understates the effect on a
4-core machine, where the old code held the whole registry's elaboration
state at once. The CI run of the re-pinned Cadence is the 4-core check.

There is no unit test in `VeilTest`: the old failure depends on the machine's
core count, so no fixed test reproduces it everywhere. The two observable
properties are the ones above: the 2-thread build succeeds, and the peak
falls. The standing check of the memory side is Cadence's CI, whose
4-core build of the Chorus model is what failed.
