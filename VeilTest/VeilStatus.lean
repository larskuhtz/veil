import VeilTest.GenCompositionBase

/-! # `#veil_status` test — the registry-only and table forms

The audit command on a module whose VC registry is in scope but whose
proofs are not: every cell reports `registry-only`, the summary counts
zero real theorems, and the `table` form prints the full greppable table.
The all-real case is pinned in `VeilTest/GenComposition.lean`. -/

open Veil

/--
warning: #veil_status CompRing: 9 cell(s) without a real theorem in scope:
initializer doesNotThrow | registry-only | — | — | —
elect doesNotThrow | registry-only | — | — | —
abstain doesNotThrow | registry-only | — | — | —
initializer leader_greatest | registry-only | — | — | —
initializer leader_unique | registry-only | — | — | —
elect leader_greatest | registry-only | — | — | —
elect leader_unique | registry-only | — | — | —
abstain leader_greatest | registry-only | — | — | —
abstain leader_unique | registry-only | — | — | —
---
info: #veil_status CompRing: 0/9 real (9 registry-only); axioms: (none)
-/
#guard_msgs in
#veil_status CompRing

/--
info: #veil_status CompRing (9 cells): action property | status | theorem | defined in | axioms
initializer doesNotThrow | registry-only | — | — | —
elect doesNotThrow | registry-only | — | — | —
abstain doesNotThrow | registry-only | — | — | —
initializer leader_greatest | registry-only | — | — | —
initializer leader_unique | registry-only | — | — | —
elect leader_greatest | registry-only | — | — | —
elect leader_unique | registry-only | — | — | —
abstain leader_greatest | registry-only | — | — | —
abstain leader_unique | registry-only | — | — | —
---
info: #veil_status CompRing: 0/9 real (9 registry-only); axioms: (none)
-/
#guard_msgs in
#veil_status CompRing table
