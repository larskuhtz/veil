import VeilTest.VCRegistryModuleConsumer

/-! # VC registry test — importer of a `module` consumer

The theorems `#prove_vc` / `#prove_action` persisted in the `module` file
`VCRegistryModuleConsumer.lean` are part of its public API. -/

/-- info: 'RegRing.ModSlice.recv_single_leader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RegRing.ModSlice.recv_single_leader

/-- info: 'RegRing.ModSlice.recv_doesNotThrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RegRing.ModSlice.recv_doesNotThrow
