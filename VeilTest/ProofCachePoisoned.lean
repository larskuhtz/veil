import VeilTest.VCRegistryBase

/-! # Poisoned proof cache — corruption must degrade to a fresh solve

The proof cache's failure contract: a
corrupt, stale, or adversarial `.vpc` entry must **fall back to a fresh
solve — never fail the build, never be accepted**. This file poisons the
cache entry of one cell in every way an entry can lie, in both hit-check
modes (`veil.cache.kernelReplay` off/on), and pins the resulting theorems
to the standard axioms (which is what "never accepted" means: a smuggled
`sorryAx` or ill-typed proof cannot survive the pin).

Poisons exercised:
1. garbage bytes (unpickle fails) — v1 mode;
2. a well-formed entry whose proof is well-typed but proves the wrong
   thing (`Meta.check` passes, `isDefEq` must reject) — v1 mode;
3. a well-formed entry whose proof is `sorryAx <stmt>` — type-correct for
   the statement, so every checker would accept it; the sorry-guard in
   `find?` must reject it (v1 mode, but the guard is mode-independent);
4. a well-formed ill-typed entry under kernel replay — the command-level
   `addDecl` must throw *synchronously*, restore the environment (a failed
   `addDecl` otherwise leaves the name occupied as an axiom), and fall
   back to a fresh solve that persists under the same name;
5. a genuine hit under kernel replay (the previous fallback re-stored a
   good entry) — must persist with the standard axioms.

A dedicated cache dir, wiped at file start, keeps this file's poison away
from any real cache and makes the phases deterministic. -/

set_option linter.unusedVariables false
set_option veil.smt.trust false
set_option veil.cache.proofs true
set_option veil.cache.dir ".lake/build/veilcache-test-poisoned"
-- Phases 1–3 test the v1 (elaborator-checked) hit path explicitly, so a
-- future default flip of `veil.cache.kernelReplay` cannot silently change
-- what they exercise; phase 4 flips it on.
set_option veil.cache.kernelReplay false
-- A command-level replay hit never elaborates the `by <tac>` suffix — the
-- unreachable-/unused-tactic linters would flag it (correctly, but by
-- design here).
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open Lean Veil RegRing

/-- The registry statement of the (recv, single_leader) cell — the cache
key every poison below targets (`#prove_vc` elaborates its proof against
exactly this `Expr`, so the discharger's cache lookup keys on it). -/
private def cellStatement : Lean.Elab.TermElabM Expr := do
  let some entries ← getVCRegistry? `RegRing
    | throwError "no VC registry for RegRing"
  let some e := entries.find? fun e =>
      e.action == `recv && e.property == `single_leader && e.kind == .primary
    | throwError "no (recv, single_leader) cell in the RegRing registry"
  return e.type

/-- Overwrite the cell's cache entry with a well-formed pickle carrying
`proof` (which need not prove the statement — that is the point). -/
private def poisonWith (proof : Expr) : Lean.Elab.TermElabM Unit := do
  let stmt ← cellStatement
  let ok ← Veil.ProofCache.store (← getOptions) stmt proof 0
  unless ok do throwError "poisoning store failed"

-- Phase 0: start from a clean, dedicated cache dir.
#eval (do
  let dir : System.FilePath := ".lake/build/veilcache-test-poisoned"
  if ← dir.pathExists then IO.FS.removeDirAll dir
  : IO Unit)

-- Phase 1: garbage bytes at the entry path — unpickle must fail ⇒ miss ⇒
-- fresh solve.
#eval (do
  let stmt ← cellStatement
  let opts ← getOptions
  IO.FS.createDirAll (Veil.ProofCache.cacheDir opts)
  IO.FS.writeFile (Veil.ProofCache.entryPath opts stmt)
    "veil poisoned-cache test: not a pickle"
  : Lean.Elab.TermElabM Unit)

namespace PoisonGarbage
#prove_vc RegRing recv single_leader by veil_solve_wp
end PoisonGarbage

/-- info: 'PoisonGarbage.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoisonGarbage.recv_single_leader

-- Phase 2: well-formed entry, well-typed proof of the WRONG thing —
-- `Meta.check` passes, `isDefEq` against the goal must reject ⇒ fresh solve.
#eval poisonWith (mkConst ``Bool.true)

namespace PoisonIllTyped
#prove_vc RegRing recv single_leader by veil_solve_wp
end PoisonIllTyped

/-- info: 'PoisonIllTyped.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoisonIllTyped.recv_single_leader

-- Phase 3: `sorryAx <stmt>` — TYPE-CORRECT for the statement, so
-- `Meta.check`/`isDefEq`/the kernel would all accept it; only `find?`'s
-- sorry-guard stands between it and a silently-`sorryAx` theorem. The pin
-- below is the actual assertion.
#eval (do
  let stmt ← cellStatement
  poisonWith (mkApp2 (mkConst ``sorryAx [levelZero]) stmt (mkConst ``Bool.false))
  : Lean.Elab.TermElabM Unit)

namespace PoisonSorry
#prove_vc RegRing recv single_leader by veil_solve_wp
end PoisonSorry

/-- info: 'PoisonSorry.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoisonSorry.recv_single_leader

-- Phase 4: kernel-replay mode. The ill-typed poison must make the
-- command-level `addDecl` throw synchronously and fall back; the fallback
-- must be able to persist under the SAME name (i.e. the failed `addDecl`'s
-- axiom-registration must have been rolled back).
set_option veil.cache.kernelReplay true

#eval poisonWith (mkConst ``Bool.true)

namespace ReplayPoisoned
#prove_vc RegRing recv single_leader by veil_solve_wp
end ReplayPoisoned

/-- info: 'ReplayPoisoned.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReplayPoisoned.recv_single_leader

-- Phase 5: the phase-4 fallback re-stored a good entry — this must now be
-- a kernel-replay hit, persisted through `addDecl` with the standard
-- axioms.
namespace ReplayHit
#prove_vc RegRing recv single_leader by veil_solve_wp
end ReplayHit

/-- info: 'ReplayHit.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ReplayHit.recv_single_leader

#eval do
  let hits ← Veil.ProofCache.statsHits
  unless hits ≥ 1 do
    throw <| IO.userError s!"expected ≥ 1 proof-cache hit (the phase-5 \
      kernel replay), got {hits}"
