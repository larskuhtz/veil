import Lean
import Veil.Base
import Veil.Frontend.DSL.Module.Representation
import Veil.Frontend.DSL.Infra.Assertions
import Veil.Frontend.DSL.Infra.Metadata
import Veil.Core.Tools.Verifier.Manager
-- Not needed for compilation, but re-exported
import Veil.Util.EnvExtensions
open Lean

namespace Veil

structure LocalEnvironment where
  currentModule : Option Module
deriving Inhabited

structure VCManagerEnvironment where
  mgr : VCManager VCMetadata SmtResult
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

/-- A channel for communicating with the VCManager. -/
initialize vcManagerCh : Std.Channel (ManagerNotification VCMetadata SmtResult) ← Std.Channel.new

/-- Info for tasks that need to be registered with `logSnapshotTask` on the main thread.
    The manager thread sends task info here, and the frontend task (runFilteredAsync)
    picks them up and registers them. -/
structure TaskRegistrationInfo where
  task : SnapshotTreeTask
  cancelTk : IO.CancelToken

/-- Channel for tasks that need snapshot registration.
    Direction: Manager → Frontend (runFilteredAsync/waitFilteredSync) -/
initialize taskRegistrationCh : Std.Channel TaskRegistrationInfo ← Std.Channel.new

/-- Prompt the frontend to read the VCManager, e.g. to print the VCs. We use a
`Condvar` instead of `Channel` because channels on the frontend thread (which
is cancellable) are subject to potential race conditions. For instance,
multiple `#gen_spec`s can be running in parallel, and one of them will "eat"
the notification from a channel, which causes the other to wait forever. With a
`Condvar`, we can `notifyAll` and check the predicate/condition holds. -/
initialize frontendNotification : Std.Condvar ← Std.Condvar.new

/-- This is to ensure we don't keep spawning server processes when `#gen_spec`
is re-elaborated in the editor. -/
initialize vcServerStarted : Std.Mutex Bool ← Std.Mutex.new false

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

namespace Frontend

open Lean.Elab.Command in
def notify : CommandElabM Unit := do
  frontendNotification.notifyAll

end Frontend

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

section ModelCheckCompilationMode

/-! ## Model Check Compilation Mode

When building a model checker binary (triggered by default `#model_check` behavior
or by background compilation), the source file is re-elaborated. This option is set
to `true` during that compilation to:
1. Skip verification-only operations (like `doesNotThrow` error reporting)
2. Skip verification commands (`#check_invariants`, `sat trace`, etc.)
3. Prevent `logError` calls from failing the build
-/

/-- Check if we're in model checking compilation mode. -/
def isModelCheckCompileMode [Monad m] [MonadOptions m] : m Bool := do
  return veil.__modelCheckCompileMode.get (← getOptions)

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

/-- Whether model-check scaffolding (FinEncodableInjOnly / Enumeration on
    `Label`, the ActionTag enum, and the EnumerableTransitionSystem) should be
    generated. See `veil.gen.modelCheckScaffolding` in `Veil/Base.lean` for the
    rationale. -/
def isModelCheckScaffoldingEnabled [Monad m] [MonadOptions m] : m Bool := do
  return veil.gen.modelCheckScaffolding.get (← getOptions)

/-- Whether the per-action *executable* extraction (`<action>.ext` and the
    label-dispatched `assembledNextAct`) should be emitted at `#gen_spec`, for
    per-label execution of actions (e.g. trace-conformance monitoring) WITHOUT
    the O(n^k) label-enumeration scaffolding of `#model_check`. See
    `veil.gen.executableActions` in `Veil/Base.lean`. -/
def isExecutableActionsEnabled [Monad m] [MonadOptions m] : m Bool := do
  return veil.gen.executableActions.get (← getOptions)

/-- Log an error, but only if not in model check compilation mode.
    In compilation mode, errors would cause lake build to fail. -/
def veilLogError [Monad m] [MonadOptions m] [AddMessageContext m] [MonadLog m]
    (msg : MessageData) : m Unit := do
  unless ← isModelCheckCompileMode do
    logError msg

/-- Log an error at a specific syntax location, but only if not in compilation mode. -/
def veilLogErrorAt [Monad m] [MonadOptions m] [AddMessageContext m] [MonadLog m]
    (stx : Syntax) (msg : MessageData) : m Unit := do
  unless ← isModelCheckCompileMode do
    logErrorAt stx msg

end ModelCheckCompilationMode

end Veil
