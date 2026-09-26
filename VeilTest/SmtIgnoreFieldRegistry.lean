import VeilTest.SmtIgnoreFieldRegistryBase

/-! # Cross-file solver-hypothesis check — the consumer

The cross-file check and prove commands read a module's instantiated
classes off the instance-implicit binders of its persisted VC statements,
so the first-order check and the withheld-field report apply on this path
too: the report appears once for the module, and the withheld field
(`SIRegOrch.totality`) never reaches the solver. -/

set_option linter.unusedVariables false

open Veil SIRegMod

set_option veil.smt.trust false

/--
info: solver hypotheses of module `SIRegMod`: every `Prop` field of its instantiated classes except the 1 withheld with `veil_smt_ignore`: `SIRegOrch.totality`
---
info: The following set of actions must preserve the invariant and successfully terminate:
  orch_step
    appended_opened ... ✅
-/
#guard_msgs in
#check_vc SIRegMod orch_step appended_opened

-- Once per module per file: the report does not repeat. The full cross-file
-- sweep and `#prove_action` (which persists an action's cells with the field
-- withheld) are asserted by the absence of errors; their cell listings are
-- informational.
#guard_msgs (drop info) in
#check_invariants SIRegMod

namespace SIRegMod.Proofs
#guard_msgs (drop info) in
#prove_action SIRegMod orch_step
end SIRegMod.Proofs
