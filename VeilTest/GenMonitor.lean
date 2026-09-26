import Veil

/-! # `#gen_monitor` test

`#gen_monitor` emits the concrete instantiation boilerplate of a
model-conformance monitor for a module elaborated with
`veil.gen.executableActions`: `Th`/`St`/`Lbl`, the theory value, the
specialized `Inhabited` seed, the instance-applied `cnext`/`cinit`,
`initStates`, and `step`. The module mirrors
`VeilTest/ExecutableActions.lean`'s toy. -/

veil module MonitorToy

type node
relation flag (n : node)

#gen_state

after_init {
  flag N := false
}

action raise (n : node) {
  require ¬ flag n
  flag n := true
}

invariant [flag_ok] True

set_option veil.gen.modelCheckScaffolding false
set_option veil.gen.executableActions true
#gen_spec

end MonitorToy

open scoped Veil.GenMonitor

#gen_monitor MonitorToy into MT
  sorts (Fin 3)
  theory (⟨⟩ : MonitorToy.Theory (Fin 3))

-- The emitted definitions have the advertised shapes.
#check (MT.initStates : List MT.St)
#check (MT.step : MT.St → MT.Lbl → List (Veil.ExecutionOutcome Int MT.St))

-- The initializer produces at least one concrete initial state …
/-- info: false -/
#guard_msgs in
#eval MT.initStates.isEmpty

-- … from which an enabled action steps successfully, and a disabled one
-- (raising an already-raised flag) does not.
/-- info: true -/
#guard_msgs in
#eval match MT.initStates with
  | st :: _ =>
    let once := (MT.step st (.raise 0)).filterMap Veil.ExecutionResult.toPostState
    let twice := once.flatMap fun st' =>
      (MT.step st' (.raise 0)).filterMap Veil.ExecutionResult.toPostState
    !once.isEmpty && twice.isEmpty
  | [] => false

/-! ## Named-argument overrides

`overrides (x := t)` passes a module argument — here the instance of an
`instantiate`d class that the concrete sort does not determine — to the
extracted executor and initializer. (`byz b` is sugar for `(nset := b)`.) -/

class Gate (node : Type) where
  open? : node → Bool

veil module MonitorGate

type node
instantiate thr : Gate node
relation flag (n : node)

#gen_state

after_init {
  flag N := false
}

action raise (n : node) {
  require thr.open? n
  flag n := true
}

invariant [flag_ok] True

set_option veil.gen.modelCheckScaffolding false
set_option veil.gen.executableActions true
#gen_spec

end MonitorGate

#gen_monitor MonitorGate into MG
  sorts (Fin 3)
  theory (⟨⟩ : MonitorGate.Theory (Fin 3))
  overrides (thr := ⟨fun n => n == 0⟩)

-- Only node 0 is open under the supplied instance.
/-- info: (true, false) -/
#guard_msgs in
#eval match MG.initStates with
  | st :: _ =>
    let ok (n : Fin 3) := !((MG.step st (.raise n)).filterMap Veil.ExecutionResult.toPostState).isEmpty
    (ok 0, ok 1)
  | [] => (false, false)
