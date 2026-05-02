theorem zero_mod_213 (a : Nat) : 0 % a = 0 := by
  by_cases h : 0 < a
  · exact Nat.mod_eq_of_lt h
  · have : a = 0 := Nat.eq_zero_of_not_pos h
    subst this
    rfl
#print axioms zero_mod_213
