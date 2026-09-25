module

public import VeilTest.Probe.Base
meta import Veil

open Lean Meta in
run_meta do
  let env ← getEnv
  let kind : ConstantInfo → String
    | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom"
    | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
    | .recInfo _ => "rec" | .quotInfo _ => "quot"
  let mut hist : Std.HashMap String Nat := {}
  let mut hiddenDefs : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    unless (`PB).isPrefixOf n do continue
    let vis := if (ci.value? (allowOpaque := true)).isSome then "+val" else "-val"
    let key := s!"{kind ci}{vis}"
    hist := hist.insert key (hist.getD key 0 + 1)
    if kind ci == "def" && vis == "-val" then hiddenDefs := hiddenDefs.push n
  let rows := hist.toList.toArray.qsort (·.1 < ·.1)
  logInfo m!"kinds: {rows.toList}"
  logInfo m!"defs without visible body ({hiddenDefs.size}): {(hiddenDefs.qsort Name.lt).toList.take 40}"
  for n in [`PB.relationalTransitionSystem, `PB.bump, `PB.user_def_inside, `PB.user_def_after,
            `PB.user_thm_inside, `PB.user_thm_after, `PB.bump_inv_c] do
    match env.find? n with
    | none => logInfo m!"{n}: NOT FOUND"
    | some ci => logInfo m!"{n}: {kind ci} value?={(ci.value? (allowOpaque := true)).isSome}"
  let g := Veil.globalEnv.getState env
  logInfo m!"globalEnv has PB: {g.containsModule `PB}"

example : PB.user_def_inside = 7 := rfl
example : PB.user_def_after = 7 := rfl
example : True := PB.user_thm_after
example : True := PB.user_thm_inside

example : PB.user_def_pub = 7 := rfl
example : PB.user_def_pub_noexpose = 7 := rfl
example : True := PB.user_thm_pub
#print axioms PB.bump_inv_c
#print axioms PB.user_thm_pub
