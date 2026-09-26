module

public import VeilTest.GenCompositionBase

/-! # `#gen_composition` test — a `module` consumer

The `module` twin of `GenComposition.lean`: cross-file `#prove_action` and
`#gen_composition` run outside any `veil module`, so their declarations
must land in this file's public API (checked by the plain importer
`GenCompositionModuleImporter.lean`). -/

set_option linter.unusedVariables false

open Veil CompRing

set_option veil.smt.trust false

namespace CompRing.Proofs
#prove_action CompRing initializer
#prove_action CompRing elect
#prove_action CompRing abstain
end CompRing.Proofs

namespace CompRing
#gen_composition CompRing
end CompRing
