import VeilTest.VCRegistryBase

/-! # Guard: `#prove_action` refuses `veil.gen.statementOnlyTheorems`

`#prove_action`'s green output means "real, kernel-checked theorems exist
now". Under `veil.gen.statementOnlyTheorems` its persistence pass would
silently write `sorryAx` stubs instead — the command must refuse before any
solving starts, rather than look proven. -/

set_option veil.gen.statementOnlyTheorems true

open Veil RegRing

/-- error: #prove_action persists real, kernel-checked proofs; `veil.gen.statementOnlyTheorems` would make it persist `sorryAx` stubs instead. Unset the option — statements are already carried, claim-free, by the VC registry (`veil.gen.vcRegistry`). -/
#guard_msgs in
#prove_action RegRing send
