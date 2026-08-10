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
    let once := (MT.step st (.raise 0)).filterMap Veil.ExecutionOutcome.toPostState
    let twice := once.flatMap fun st' =>
      (MT.step st' (.raise 0)).filterMap Veil.ExecutionOutcome.toPostState
    !once.isEmpty && twice.isEmpty
  | [] => false
