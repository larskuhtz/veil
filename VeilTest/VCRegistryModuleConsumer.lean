module

public import VeilTest.VCRegistryBase

/-! # VC registry test — a `module` consumer

The cross-file persistence commands run *outside* any `veil module`, so in a
`module` file their theorems would be file-private (invisible to importers)
unless the commands emit into the public scope. This file persists cells of
`VCRegistryBase.lean`'s registry; `VCRegistryModuleImporter.lean` (a plain
file) must see them. -/

set_option linter.unusedVariables false

open Veil RegRing

set_option veil.smt.trust false

namespace RegRing.ModSlice
#prove_vc RegRing recv single_leader by veil_solve_wp
#prove_action RegRing recv
end RegRing.ModSlice
