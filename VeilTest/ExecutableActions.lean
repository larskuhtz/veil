import Veil

/- Test for `veil.gen.executableActions`: with model-check scaffolding
   OFF, the per-action executable extraction (`NextAct.extracted`, the
   label-dispatched executor) must still be generated — WITHOUT the O(n^k)
   `EnumerableTransitionSystem`/`Enumeration` label scaffolding. -/
veil module ExecActToy

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

end ExecActToy

-- Present: the per-label executable dispatcher (feature under test).
#check @ExecActToy.NextAct.extracted
