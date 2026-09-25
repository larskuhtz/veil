module

public import Veil

veil module PB

type node

relation r : node → Bool
individual c : Nat

#gen_state

after_init {
  r N := false
  c := 0
}

action bump (n : node) {
  r n := true
  c := c + 1
}

invariant [inv_c] c ≥ 0
invariant [inv_r] r N ∨ ¬ r N

#gen_spec

#gen_theorems

theorem user_thm_inside : True := trivial

def user_def_inside : Nat := 7

end PB

-- After `end`: outside the public/expose scope `veil module` opens.
theorem PB.user_thm_after : True := trivial
def PB.user_def_after : Nat := 7

public section
theorem PB.user_thm_pub : True := trivial
@[expose] def PB.user_def_pub : Nat := 7
def PB.user_def_pub_noexpose : Nat := 7
end
