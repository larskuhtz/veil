module

public meta import Lean
public meta import Veil.Base
public meta import Veil.Frontend.DSL.Module.Representation
public meta import Veil.Frontend.DSL.Infra.Assertions
public meta import Veil.Frontend.DSL.Infra.Metadata
-- Not needed for compilation, but re-exported
public meta import Veil.Util.EnvExtensions

public meta section
open Lean

namespace Veil

structure LocalEnvironment where
  currentModule : Option Module
deriving Inhabited

structure GlobalEnvironment where
  modules : Std.HashMap Name Module
  assertions : AssertionEnvironment
deriving Inhabited

def GlobalEnvironment.containsModule (genv : GlobalEnvironment) (name : Name) : Bool :=
  genv.modules.contains name

initialize localEnv : SimpleScopedEnvExtension LocalEnvironment LocalEnvironment ←
  registerSimpleScopedEnvExtension {
    initial := { currentModule := none}
    addEntry := fun _ s' => s'
  }

initialize globalEnv : SimpleScopedEnvExtension GlobalEnvironment GlobalEnvironment ←
  registerSimpleScopedEnvExtension {
    initial := default
    addEntry := fun _ s' => s'
  }

/-! ## Persistent VC registry (`veil.gen.vcRegistry`)

The olean-carried record of a module's verification conditions, written at
`#gen_spec` when `veil.gen.vcRegistry` is enabled. Importing files can
reconstruct the module's VCs — with *identical* statements, since the
elaborated `Expr` is persisted, never re-generated — and check or prove them
cross-file (`#check_invariants <Module>`, `#check_action <Module> <action>`,
`#prove_action <Module> <action>`). This is the persistence layer the
file-local `localEnv` module state deliberately is not. -/

/-- One VC of a module, as persisted in the registry. Mirrors
`VCData VCMetadata` for induction VCs, but carries only serializable data
(no closures, no dischargers) plus the pre-elaborated statement `type`. -/
structure VCRegistryEntry where
  /-- The VC name (module-relative), e.g. `vote_agreement_pos`. Also the base
  name under which `#gen_theorems`/`#prove_action` persist the theorem. -/
  name : Name
  /-- The action (or initializer) this VC is about. -/
  action : Name
  /-- The property this VC is about (invariant/safety name, or
  `doesNotThrow`). -/
  property : Name
  /-- Primary or alternative form (the WP/TR pairing of a cell). -/
  kind : InductionVCKind
  /-- Discharge style: `wp` (VeilM semantics) or `tr` (Transition
  semantics). Determines the discharge tactic on the cross-file path. -/
  style : VCStyle
  /-- Statement binders, as written by VC generation (display/stub use). -/
  params : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)
  /-- Statement syntax, as written by VC generation (display/stub use). -/
  statement : Term
  /-- The fully-elaborated, closed statement. This is the ground truth the
  cross-file commands elaborate proofs against. -/
  type : Expr
deriving Inhabited

/-- module name ↦ its VC registry, accumulated over imports. A module
appearing in several imported oleans (impossible for well-formed builds)
resolves to the last-imported entry. -/
initialize vcRegistryExt :
    SimplePersistentEnvExtension (Name × Array VCRegistryEntry)
      (NameMap (Array VCRegistryEntry)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, es) => m.insert n es
    addImportedFn := fun ess =>
      ess.foldl (init := {}) fun m es =>
        es.foldl (init := m) fun m (n, e) => m.insert n e
  }

/-- The persisted VC registry of `modName`, if any. The extension state folds
imported entries and current-file entries (current file wins, being added
last). -/
def getVCRegistry? [Monad m] [MonadEnv m] (modName : Name) :
    m (Option (Array VCRegistryEntry)) := do
  return (vcRegistryExt.getState (← getEnv)).find? modName

/-- Module names that have a persisted VC registry in scope (for error
messages). -/
def vcRegistryModules [Monad m] [MonadEnv m] : m (Array Name) := do
  return (vcRegistryExt.getState (← getEnv)).toList.map (·.1) |>.toArray

/-- Transient marker (never persisted): whether some command of the current
file elaboration has already started/reset the VC manager. The first
cross-file check command of a file must reset the manager exactly once
(matching `#gen_spec`'s behavior); later commands in the same elaboration
must not, or they would drop each other's in-flight VCs. -/
structure VerifierArmedState where
  armed : Bool := false
deriving Inhabited

initialize verifierArmedExt : SimpleScopedEnvExtension VerifierArmedState VerifierArmedState ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun _ s' => s'
  }

def localEnv.modifyModule [Monad m] [MonadEnv m] (f : Option Module → Module) : m Unit :=
  localEnv.modify (fun s => { s with currentModule := f s.currentModule })

def getCurrentModule [Monad m] [MonadEnv m] [MonadError m] (errMsg : MessageData := m!"getCurrentModule called outside of a module") : m Module := do
  if let some mod := (← localEnv.get).currentModule then
    return mod
  else
    throwError errMsg

def mkNewAssertion [Monad m] [MonadEnv m] [MonadError m] (proc : Name) (stx : Syntax) : m AssertionId := do
  let mod ← getCurrentModule (errMsg := "Cannot have a Veil assertion outside of a module")
  let gctx ← globalEnv.get
  let actx := gctx.assertions
  let assert := { id := actx.maxId, ctx := { module := mod.name, procedure := proc, stx := stx } }
  let actx' := { actx with maxId := actx.maxId + 1, find := actx.find.insert actx.maxId assert }
  globalEnv.modify (fun gctx => { gctx with assertions := actx' })
  return actx.maxId

section DevelopingTools

open Lean Meta Elab Command in
elab "veil_set_option " o:ident v:term : command => do
  let lenv ← localEnv.get
  let some mod := lenv.currentModule | throwError s!"Not in a module"
  let v ← liftTermElabM <| Term.elabTerm v (mkConst ``Bool)
  let b := if v == mkConst ``Bool.true then true else false
  match o.getId with
  | `useLocalRPropTC => localEnv.modifyModule (fun _ => { mod with _useLocalRPropTC := b })
  | _ => throwError s!"Unsupported option {o}"

end DevelopingTools

section VerificationModes

/-- Whether verification is disabled for this elaboration: the `veil.noVerify`
    option, or the `VEIL_NO_VERIFY` environment variable (any value except
    empty or `0`). Under this mode `#gen_spec` generates VC statements but
    starts no solving, and every check/trace/model-check/theorem-persistence
    command logs a visible `⏭ skipped` warning and returns. Intended for
    editor sessions on large models — see `veil.noVerify` in `Veil/Base.lean`. -/
def isNoVerifyMode [Monad m] [MonadOptions m] [MonadLiftT IO m] : m Bool := do
  if veil.noVerify.get (← getOptions) then return true
  match (← (IO.getEnv "VEIL_NO_VERIFY" : IO (Option String))) with
  | some v => return v != "" && v != "0"
  | none => return false

end VerificationModes

end Veil
