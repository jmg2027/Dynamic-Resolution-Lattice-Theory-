import E213.Kernel.Tactic.Nat213

/-!
# 213-native `Nat` div/mod helpers (∅-axiom, Math layer)

Lean-core `Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`,
`Nat.div_lt_iff_lt_mul`, `Nat.div_mul_le_self`, `Nat.add_div_right`,
`Nat.add_mod_right` all bring `propext`.  These ∅-axiom replacements
unblock the Pell/Trib FSM ↪ BitFSM lens cluster.
-/

namespace E213.Math.NatHelpers.NatDiv213

open E213.Tactic.Nat213 (sub_add_cancel add_sub_cancel_right)

/-- `(a + n) / n = a / n + 1` when `0 < n`.  ∅-axiom. -/
theorem add_div_right_pos {n : Nat} (hn : 0 < n) (a : Nat) :
    (a + n) / n = a / n + 1 := by
  rw [Nat.div_eq (a + n) n]
  rw [if_pos ⟨hn, Nat.le_add_left n a⟩]
  rw [add_sub_cancel_right]

/-- `(a + n) % n = a % n` when `0 < n`.  ∅-axiom. -/
theorem add_mod_right_pos {n : Nat} (hn : 0 < n) (a : Nat) :
    (a + n) % n = a % n := by
  rw [Nat.mod_eq (a + n) n]
  rw [if_pos ⟨hn, Nat.le_add_left n a⟩]
  rw [add_sub_cancel_right]

/-- `a / b * b ≤ a`.  ∅-axiom via strong recursion. -/
theorem div_mul_le_self : ∀ (a b : Nat), a / b * b ≤ a := fun a b =>
  Nat.strongRecOn a (motive := fun a => a / b * b ≤ a) fun a ih => by
    show a / b * b ≤ a
    by_cases hbound : 0 < b ∧ b ≤ a
    · have hsub_lt : a - b < a :=
        Nat.sub_lt (Nat.lt_of_lt_of_le hbound.1 hbound.2) hbound.1
      have ih' := ih (a - b) hsub_lt
      have hd : a / b = (a - b) / b + 1 := by
        rw [Nat.div_eq]; rw [if_pos hbound]
      have h1 : a / b * b = (a - b) / b * b + b := by
        rw [hd]; rw [Nat.succ_mul]
      rw [h1]
      exact Nat.le_trans (Nat.add_le_add_right ih' b)
        (Nat.le_of_eq (sub_add_cancel hbound.2))
    · have hd : a / b = 0 := by
        rw [Nat.div_eq]; rw [if_neg hbound]
      rw [hd, Nat.zero_mul]; exact Nat.zero_le _

/-- `a < b * m → a / b < m`.  ∅-axiom replacement for
    `(Nat.div_lt_iff_lt_mul hb).mpr`. -/
theorem div_lt_of_lt_mul {b m a : Nat} (h : a < b * m) : a / b < m := by
  rcases Nat.lt_or_ge (a / b) m with hlt | hge
  · exact hlt
  · exfalso
    have hmul : b * m ≤ b * (a / b) := Nat.mul_le_mul_left b hge
    have hcomm : b * (a / b) = a / b * b := Nat.mul_comm b (a / b)
    have hself : a / b * b ≤ a := div_mul_le_self a b
    exact Nat.lt_irrefl a
      (Nat.lt_of_lt_of_le h (Nat.le_trans (hcomm ▸ hmul) hself))

end E213.Math.NatHelpers.NatDiv213
