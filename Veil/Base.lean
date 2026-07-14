import Lean
open Lean

/-! # Veil

Veil is a _foundational_ framework for (1) specifying, (2)
implementing, (3) testing, and (4) proving safety (and, in the future,
liveness) properties of state transition systems, with a focus on
distributed protocols.

Veil is embedded in the Lean 4 proof assistant and provides push-button
verification for transition systems and their properties expressed
decidable fragments of first-order logic, with the full power of a
modern higher-order proof assistant available when automation falls
short.

This file serves as the root of the `Veil` library. It provides
definitions, options, and attributes that are used throughout the
framework.
-/

/-! ## Trace classes -/

initialize
  registerTraceClass `veil (inherited := true)
  registerTraceClass `veil.info
  registerTraceClass `veil.warning
  registerTraceClass `veil.debug
  registerTraceClass `veil.cache
  registerTraceClass `veil.desugar
  registerTraceClass `veil.wp
  registerTraceClass `veil.timing
  registerTraceClass `veil.extraction
  -- Performance trace classes (integrate with Lean's profiler)
  registerTraceClass `veil.perf (inherited := true)
  registerTraceClass `veil.perf.elaborator
  registerTraceClass `veil.perf.tactic
  registerTraceClass `veil.perf.extract
  registerTraceClass `veil.perf.smt
  registerTraceClass `veil.perf.definition
  registerTraceClass `veil.perf.discharger

/-! ## Options -/

namespace Veil
/-- Veil does some pretty crazy stuff, so we override some of Lean's defaults
when you open a `veil module`. -/
def veilDefaultOptions : List (Name × DataValue) := [
  -- Helpful when elaborating nested procedures.
  (`maxRecDepth, DataValue.ofNat 1024),
  -- Needed because the model checker produces the code for the transition
  -- system (partly) via typeclass inference.
  -- Back to 500000: an earlier 1000000
  -- raise was for `#gen_state` on a ~50-component module sitting at the
  -- boundary — but this module default applies to the WHOLE module
  -- elaboration (every discharger captures it at `#gen_spec`), and a global
  -- heartbeat doubling is the prime suspect for a measured sweep-wall
  -- regression. The `#gen_state` raise now lives scoped in the elaborator
  -- (`Module.ensureStateIsDefined`), the one site that needs it; a
  -- file-level `set_option` does not reach that site.
  (`maxHeartbeats, DataValue.ofNat 500000),
  (`synthInstance.maxSize, DataValue.ofNat 4096),
]

register_option veil.printCounterexamples : Bool := {
  defValue := true
  descr := "Print counterexamples (models) when they are found in `#check_invariants`."
}

register_option veil.unfoldGhostRel : Bool := {
  defValue := true
  descr := "If true, `veil_fol` will unfold ghost relations during \
  simplification. This is the behaviour in Veil 1.0. Otherwise, it \
  will use small-scale axiomatization. This option must be set before `#gen_spec`."
}

register_option veil.desugarTactic : Bool := {
  defValue := false
  descr := "If true, Veil-specific tactics will be desugared and the \
  desugared version will be displayed as a suggestion. \
  Note that the formatting of the desugared version depends on **whether \
  the original tactic is placed in isolation** (i.e., whether the lines \
  it spans contain only whitespace characters other than the tactic itself)."
}


register_option veil.violationIsError : Bool := {
  defValue := true
  descr := "If true, violations found by verification or model checking are \
  logged as errors. If false, they are logged as info messages."
}

register_option veil.__modelCheckCompileMode : Bool := {
  defValue := false
  descr := "(INTERNAL ONLY. DO NOT USE.) When true, skip verification-only operations for model checking compilation."
}

register_option veil.gen.vcRegistry : Bool := {
  defValue := false
  descr := "When true, `#gen_spec` persists the module's VC registry into the \
  olean: for every generated verification condition, its name, action, \
  property, kind, style, statement syntax, and fully-elaborated statement \
  (as an `Expr`). Files importing the module can then run \
  `#check_invariants <Module>`, `#check_action <Module> <action>`, \
  `#check_vc <Module> <action> <property>`, and `#prove_action <Module> \
  <action>` cross-file, against exactly the statements this module's own \
  sweep would check — the statements are read from the registry, never \
  re-generated, so they cannot drift. Costs one statement elaboration per \
  VC at `#gen_spec` plus olean size (~2 KB/VC)."
}

register_option veil.noVerify : Bool := {
  defValue := false
  descr := "When true, Veil elaborates specifications without running any \
  verification. `#gen_spec` still elaborates the full specification and \
  generates all VC statements, but does not start the background \
  `doesNotThrow` checks; `#check_invariants`/`#check_action`, trace \
  queries (`sat`/`unsat trace`), `#model_check`, and `#gen_theorems` log \
  a visible '⏭ skipped' warning instead of solving. Intended for opening \
  large models in an editor without paying their verification cost. The \
  `VEIL_NO_VERIFY` environment variable (any value except empty or `0`) is \
  equivalent to this option — set it in the *editor's* environment so \
  language-server sessions skip solving while `lake build` from a clean \
  shell is unaffected. NOTE: an elaboration under this mode checks and \
  persists no VC theorems — never enable it for builds whose artifacts \
  (oleans) are consumed downstream."
}

inductive VeilSolver : Type where
  | smt
  | grind
  | grindAndSMT
  | custom

instance : Inhabited VeilSolver := ⟨.smt⟩

instance : ToString VeilSolver where
  toString
    | .smt => "smt"
    | .grind => "grind"
    | .grindAndSMT => "grindAndSMT"
    | .custom => "custom"

instance : Lean.KVMap.Value VeilSolver where
  toDataValue s := toString s
  ofDataValue?
    | .ofString "smt" => some .smt
    | .ofString "grind" => some .grind
    | .ofString "grind+smt" => some .grindAndSMT
    | .ofString "custom" => some .custom
    | _ => none

register_option veil.solver : VeilSolver := {
  defValue := .smt
  descr := "Solver strategy used by `veil_solve`.
   - `smt` uses `veil_smt`
   - `grind` uses Lean's `grind`
   - `grind+smt` tries `grind` first, then falls back to `veil_smt`
   - `custom` uses a user-provided `veil_solve` tactic

  For `custom`, define a macro such as
  ```lean
  macro_rules
  | `(tactic| veil_solve) => `(tactic| <your tactic here>)
  ```"
}

register_option veil.smt.finiteModelFind : Bool := {
  defValue := true
  descr := "If true, the SMT solver will use finite model finding mode (finite-model-find). \
  If you work in a decidable fragment, this will tend to speed things up. \
  NOTE: dischargers capture solver options at `#gen_spec` (VC generation), \
  so this must be set before `#gen_spec`; setting it only around a check \
  command has no effect on solving."
}

register_option veil.smt.trust : Bool := {
  defValue := true
  descr := "If true, `veil_smt` trusts unsat results from the SMT solver. \
  If false, `veil_smt` asks the SMT backend to reconstruct Lean proofs. \
  NOTE: dischargers capture solver options at `#gen_spec` (VC generation), \
  so this must be set before `#gen_spec`; setting it only around a check \
  command has no effect on solving."
}

register_option veil.smt.timeout : Nat := {
  defValue := 60
  descr := "Timeout for the SMT solver in seconds. Default is 60 seconds. \
  NOTE: dischargers capture solver options at `#gen_spec` (VC generation), \
  so this must be set before `#gen_spec`; setting it only around a check \
  command has no effect on solving."
}

register_option veil.smt.seed : Nat := {
  defValue := 0
  descr := "Random seed for the SMT solver (cvc5 `seed` and `sat-random-seed`). \
  0 (the default) leaves the solver's own default seed in place; any other \
  value is passed through. Retry attempts (`veil.smt.retries`) perturb this \
  to escape seed-dependent e-matching divergence. Like all solver options, \
  must be set before `#gen_spec`."
}

register_option veil.smt.retries : Nat := {
  defValue := 1
  descr := "How many times to re-dispatch a VC whose SMT query timed out, \
  before reporting ⏱. Each retry uses a fresh random seed (`veil.smt.seed` = \
  attempt index) and a budget of `veil.smt.retryTimeout` seconds. Retries \
  only fire after a *timeout* (not after `sat`, genuine `unknown`, or \
  errors) and are reported distinctly in the summary so flakiness stays \
  visible. Set to 0 to disable. Must be set before `#gen_spec`."
}

register_option veil.smt.retryTimeout : Nat := {
  defValue := 120
  descr := "Timeout (in seconds) for retry attempts (see `veil.smt.retries`). \
  Timeout-then-fast-success is a seed artifact: such queries either finish \
  quickly under a fresh seed or never, so a short budget avoids burning \
  another full `veil.smt.timeout` on genuinely divergent queries. \
  Must be set before `#gen_spec`."
}

register_option veil.gen.strictLocalSimp : Bool := {
  defValue := true
  descr := "If true (default), failing to synthesize the local \
  pre-simplification infrastructure (LocalTheoryProp/LocalRProp simplified \
  cores and the local `meetsSpecificationIfSuccessful` theorems) at \
  `#gen_spec` is a hard error. Without this infrastructure every VC \
  re-simplifies the full assembled assertion clump from scratch, silently \
  degrading `#check_invariants` roughly 10x on large modules; the failure is \
  usually instance-search budget exhaustion, fixed by raising \
  `synthInstance.maxHeartbeats`/`synthInstance.maxSize`/`maxRecDepth`. \
  Set to false to restore the old warn-and-continue behavior."
}

register_option veil.report.slowVCs : Nat := {
  defValue := 10
  descr := "Number of slowest verification conditions to list at the end of \
  `#check_invariants` (ranked by individual discharger time, including failed \
  attempts, which burn the full timeout). Set to 0 to disable the report."
}

register_option veil.report.slowVCsMinMs : Nat := {
  defValue := 5000
  descr := "Minimum discharge time (in milliseconds) for an attempt to appear \
  in the slowest-VCs report; when no attempt qualifies, the report is \
  omitted entirely. The default floor keeps `#check_invariants` output \
  deterministic for fast specifications (e.g. under `#guard_msgs` in tests) \
  while still surfacing the tail on long-running sweeps. Lower it to \
  investigate moderately slow VCs."
}

register_option veil.report.nearTimeoutPercent : Nat := {
  defValue := 50
  descr := "In the slowest-VCs report, flag a discharge attempt as \
  near-timeout (⚠️) when its time exceeds this percentage of \
  `veil.smt.timeout`. Near-timeout VCs are divergence candidates: a small \
  model change (e.g. one added invariant) may push them past the timeout."
}

register_option veil.report.witnessSizes : Bool := {
  defValue := false
  descr := "If true, measure the heap size (DAG-aware object count, \
  `Lean.Expr.numObjs`) of every successful discharger's proof witness and \
  append a summary report to the verification results. Diagnostic \
  instrumentation for the witness-size blowup of large modules (each WP \
  witness embeds the full normalisation chain of its action against the \
  assembled invariant clump); off by default so command output stays \
  deterministic. The registry is cumulative per Lean module elaboration; \
  when several check commands run in one module, later measurements of the \
  same discharger win."
}

register_option veil.experimental.wpCompact : Bool := {
  defValue := true
  descr := "Experimental. If true, compact generated `wp_local_eq.pred` definitions by sharing duplicated postcondition branches with `letEq` and exposing abstract-state conditionals field-wise."
}

register_option veil.lazyWitnessRegen : Bool := {
  defValue := true
  descr := "If true (default), drop the proof witness Expr from \
  `DischargerResult.proven` after a discharger succeeds and re-elaborate it \
  on demand at `#gen_theorems` time. Trades one-time regeneration cost for \
  bounded steady-state heap during `#check_invariants` (large protocols that \
  previously OOM'd can complete). Set to false to retain witnesses eagerly \
  (the pre-2026-06-10 behavior); useful for debugging regen behavior or when \
  `#gen_theorems` is called repeatedly on the same VCs and the per-call regen \
  cost dominates the memory savings."
}

register_option veil.gen.statementOnlyTheorems : Bool := {
  defValue := false
  descr := "If true, `#gen_theorems` persists statement-only stubs (a \
  `sorryAx` of each VC statement) instead of proofs — and does so \
  SOLVE-FREE: it neither starts nor awaits any discharger, since the \
  statements exist from `#gen_spec`'s SMT-free VC generation and a stub \
  carries no verification claim (both the WP and TR encodings of every \
  cell are stubbed; VCs a preceding check command terminally failed are \
  skipped). This is a compatibility mode: the preferred statement carrier \
  is the claim-free VC registry (`veil.gen.vcRegistry`), which importing \
  files can re-prove for real (`#prove_action`). Historical note: \
  previously this mode awaited the full sweep and \
  stubbed exactly the proven VCs, so a stub certified a checked-then- \
  discarded proof — that reading is dead, a stub now certifies nothing. \
  Downstream axiom pins over stubs show `sorryAx`; anything real must be \
  re-proven from the registry. Mutually exclusive with \
  `veil.gen.streamTheorems` in intent (retention is pointless when only \
  statements are persisted), and rejected by `#prove_action` (a \
  proof-persistence command must never emit stubs)."
}

register_option veil.gen.streamTheorems : Bool := {
  defValue := false
  descr := "If true, dischargers retain their full proof witness after a \
  successful discharge (instead of dropping it, `veil.lazyWitnessRegen`) so \
  that `#gen_theorems` can persist each proven VC incrementally — while the \
  sweep is still running — and release the witness immediately after adding \
  its theorem to the environment. This is the scalable persistence mode for \
  proof-reconstruction runs (`veil.smt.trust false`), where the trusted-stub \
  fast path (`veil.gen.trustedTheoremStubs`) does not apply and lazy witness \
  regeneration would re-run every proof reconstruction serially after the \
  sweep. Like all discharger behavior, retention is captured at `#gen_spec` — \
  set this option before `#gen_spec`, and only in modules that run \
  `#gen_theorems` (without it, retained witnesses are never released and \
  peak memory grows by the total witness mass). Inert under \
  `veil.smt.trust = true`: trusted witnesses are persisted as statement-only \
  stubs and are never retained in full."
}

register_option veil.cache.proofs : Bool := {
  defValue := false
  descr := "If true, the Veil discharge tactics (`veil_solve_wp`, \
  `veil_solve_tr`, `veil_solve_wp_doesnotthrow`) consult a content-addressed \
  on-disk proof cache (`veil.cache.dir`) before searching, and store every \
  successful sorry-free proof term after. Reconstruction mode only \
  (`veil.smt.trust false`): trusted-mode discharges are never cached. The \
  cache key is the closed goal statement itself (the stored entry carries \
  the full statement `Expr`; a hash collision is a miss, never a wrong \
  answer), so it is solver- and option-independent — a cached proof either \
  re-checks against the live goal and environment (`Meta.check` + `isDefEq` \
  on every hit; the kernel still checks at every persistence point) or it \
  is treated as a miss and re-solved. Failures, timeouts, and \
  counterexamples are never cached (they must stay retryable / \
  re-findable). Read at tactic runtime: for in-file sweeps set it before \
  `#gen_spec` (discharger option capture); in cross-file consumers a \
  file-level `set_option` works as written. Per-hit detail on \
  `trace.veil.cache`; sweep output reports one ♻ summary line."
}

register_option veil.cache.dir : String := {
  defValue := ".lake/build/veilcache"
  descr := "Directory of the on-disk proof cache (`veil.cache.proofs`), \
  relative to the process working directory (the workspace root under \
  `lake build` and in the language server). One file per cached proof, \
  named by the statement hash; safe to delete at any time (the cache only \
  ever skips proof *search*, never checking)."
}

register_option veil.cache.maxAgeDays : Nat := {
  defValue := 14
  descr := "Age cutoff (days) for proof-cache entries (`veil.cache.proofs`; \
  At the first successful store of a process, \
  entries whose file modification time is older than this are deleted \
  (plus day-old `.tmp` strays). Store-time only, once per process: a \
  fully-warm build (no stores) never pays the directory scan. Hits do NOT \
  refresh an entry's mtime, so an entry that only ever hits re-solves once \
  per cutoff period and re-enters fresh — the price of not touching files \
  on the hit path. 0 disables GC entirely."
}

register_option veil.cache.kernelReplay : Bool := {
  defValue := true
  descr := "If true (default — measured 3.3x cheaper than \
  the elaborator re-check at large-witness scale, and stronger), \
  proof-cache hits (`veil.cache.proofs`) are checked by \
  the KERNEL instead of the elaborator. \
  Persistence commands (`#prove_vc` and `#prove_action` cells) consult \
  the cache at the command level and hand the cached \
  term straight to `addDecl` — the kernel type-check IS the hit re-check — \
  skipping tactic entry and the elaborator's `Meta.check`+`isDefEq`. \
  Check-only discharges (sweep dischargers) kernel-check the cached term \
  against a discarded scratch environment, which is *stronger* checking \
  than a fresh sweep ✅ (elaborator-checked). A kernel rejection degrades \
  to a miss and a fresh solve, so a stale or corrupt entry can never fail \
  a build. No mode ever skips the check on a hit — this option only \
  selects WHICH checker runs, and \
  where. Like `veil.cache.proofs`, read at tactic/command runtime on the \
  cross-file paths (a file-level `set_option` works as written \
  there); for in-file sweeps set it before `#gen_spec`. Note: a \
  command-level replay hit never elaborates the command's `by <tac>` \
  suffix, so the unreachable-/unused-tactic linters flag it — set \
  `linter.unreachableTactic`/`linter.unusedTactic` to false in files that \
  expect hits."
}

register_option veil.gen.trustedTheoremStubs : Bool := {
  defValue := true
  descr := "If true (default), `#gen_theorems` persists a VC theorem whose \
  discharge was trusted-SMT-based (`veil.smt.trust = true`, witness contains \
  `sorryAx`) as a direct `sorryAx` of the VC statement, instead of \
  re-elaborating the discharger (lazy witness regeneration — a second, \
  serial SMT run per VC) or retaining the full `Eq.mpr` normalisation chain \
  (~100 KB–10 MB per VC). The trust base is unchanged — the chain's leaf is \
  the same axiom — but memory and olean cost become O(statement) per \
  theorem, which is what lets `#gen_theorems` scale to large modules under \
  trust mode. Proof-reconstruction runs (`veil.smt.trust = false`) are \
  unaffected: their witnesses contain no `sorryAx` and are materialised in \
  full as before. Set to false to restore the previous behavior (full \
  witness even under trust mode)."
}

end Veil
