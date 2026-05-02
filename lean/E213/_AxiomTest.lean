-- Direct sub_pos_of_lt
theorem sub_pos_of_lt_p {a b : Nat} (h : a < b) : 0 < b - a := by
  induction a generalizing b with
  | zero => 
    show 0 < b - 0
    rw [Nat.sub_zero]; exact h
  | succ k ih => 
    cases b with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ m =>
      show 0 < m + 1 - (k + 1)
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih (Nat.lt_of_succ_lt_succ h)
#print axioms sub_pos_of_lt_p
