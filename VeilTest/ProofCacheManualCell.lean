import VeilTest.VCRegistryBase

/-! # Proof cache on the MANUAL-cell path (`#prove_vc … by <tactic>`)

`withProofCache` — for a long time the only `ProofCache.store` call site —
wraps exactly three tactic dispatch entries: `veil_solve_wp`,
`veil_solve_wp_doesnotthrow`, `veil_solve_tr`. A project that discharges
cells with its own script (say `unveil <;> simp <;> grind`) therefore *read*
from the cache and never wrote to it, so it could never register a hit. Every
other cache test here proves with `veil_solve_wp`, i.e. exactly the one
configuration that already worked.

This file pins the manual path. `Source` proves the cell with the cache
switched **off**, so it deposits nothing; the two manual `#prove_vc`s below
discharge by `exact` — not a `veil_solve_*` dispatch, so `withProofCache` is
not involved at all. The first must therefore store via `elabProveVC` itself,
and the second must hit.

Note `veil.smt.trust` is left at its default `true` on purpose: the cache used
to be gated on it, which disabled it outright for solver-free projects that
have no reason to set it false. The gate was redundant — a sorry-carrying
proof is refused independently at every store site and re-checked by
`ProofCache.find?` on read.

`hits ≥ 1` rather than an exact count: the cache directory survives across
builds by design, so on a re-elaboration the first manual `#prove_vc` may hit
too. A dedicated directory keeps these entries away from other tests. -/

set_option linter.unusedVariables false
set_option veil.cache.dir ".lake/build/veilcache-manualcell"
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Veil RegRing

-- Cache OFF: produces the proof term the manual cells reuse, without
-- depositing anything itself.
namespace Source
set_option veil.smt.trust false in
set_option veil.cache.proofs false in
#prove_vc RegRing recv single_leader by veil_solve_wp
end Source

set_option veil.cache.proofs true

-- Manual discharge, cold cache: `elabProveVC` must be the writer.
namespace ManualStore
#prove_vc RegRing recv single_leader by exact Source.recv_single_leader
end ManualStore

-- Identical registry statement: must hit.
namespace ManualHit
#prove_vc RegRing recv single_leader by exact Source.recv_single_leader
end ManualHit

#eval do
  let hits ← Veil.ProofCache.statsHits
  unless hits ≥ 1 do
    throw <| IO.userError
      s!"expected ≥ 1 proof-cache hit on the manual-cell path, got {hits}"

/-- info: 'ManualHit.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ManualHit.recv_single_leader
