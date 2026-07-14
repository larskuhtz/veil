import VeilTest.VCRegistryBase

/-! # Content-addressed proof cache (`veil.cache.proofs`)

Two `#prove_vc`s of the same cell in one file: the first solve stores its
reconstructed proof in the on-disk cache, the second must *hit* — under
the default `veil.cache.kernelReplay` the cached term is
consumed at the command level and its persisting `addDecl` IS the kernel
check, so its axiom pin is the standard three-axiom form (the cache skips
search, never checking). The v1 elaborator-checked hit path is pinned
separately in `ProofCachePoisoned.lean`.

The assertion is `hits ≥ 1` rather than an exact count: the cache directory
persists across builds by design, so on a re-elaboration the *first*
`#prove_vc` may hit too (that is the cache doing its job across builds, not
a failure). A dedicated test cache dir keeps this file's entries away from
any real project cache. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.cache.proofs true
set_option veil.cache.dir ".lake/build/veilcache-test"
-- A command-level replay hit never elaborates the `by <tac>` suffix — the
-- unreachable-/unused-tactic linters would flag it (by design here).
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Veil RegRing

namespace CacheFirst
#prove_vc RegRing recv single_leader by veil_solve_wp
end CacheFirst

namespace CacheSecond
-- Identical statement (the registry `Expr`): must be a cache hit.
#prove_vc RegRing recv single_leader by veil_solve_wp
end CacheSecond

#eval do
  let hits ← Veil.ProofCache.statsHits
  unless hits ≥ 1 do
    throw <| IO.userError s!"expected ≥ 1 proof-cache hit, got {hits}"

-- A cached proof persists through `addDecl` with the standard axioms —
-- indistinguishable from a fresh solve in trust terms.
/-- info: 'CacheFirst.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CacheFirst.recv_single_leader

/-- info: 'CacheSecond.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CacheSecond.recv_single_leader
