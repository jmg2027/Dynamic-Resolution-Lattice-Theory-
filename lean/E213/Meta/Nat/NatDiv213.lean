import E213.Meta.Tactic.NatHelper

/-!
# 213-native `Nat` div/mod helpers (∅-axiom, Math layer)

Lean-core `Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`,
`Nat.div_lt_iff_lt_mul`, `Nat.div_mul_le_self`, `Nat.add_div_right`,
`Nat.add_mod_right` all bring `propext`.  These ∅-axiom replacements
unblock the Pell/Trib FSM ↪ BitFSM lens cluster.
-/

namespace E213.Meta.Nat.NatDiv213

open E213.Tactic.NatHelper (sub_add_cancel add_sub_cancel_right)

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

/-- `k * b / b = k` (`0 < b`), by induction on `k`.  ∅-axiom
    (Lean-core `Nat.mul_div_cancel` pulls `propext`). -/
theorem mul_div_self_pure (k b : Nat) (h : 0 < b) : k * b / b = k := by
  induction k with
  | zero => rw [Nat.zero_mul]; exact Nat.zero_div b
  | succ j ih => rw [Nat.succ_mul, add_div_right_pos h (j * b), ih]

/-- Left-cancel `a * b / a = b` (`0 < a`), via `mul_div_self_pure`.  ∅-axiom. -/
theorem mul_div_cancel_left_pure (a b : Nat) (h : 0 < a) : a * b / a = b := by
  rw [Nat.mul_comm a b]; exact mul_div_self_pure b a h

/-- `a / b ≤ a` when `0 < b`.  ∅-axiom replacement for Lean-core
    `Nat.div_le_self` (which pulls `propext` via `Nat.div_zero`).
    Proof: `a/b ≤ a/b * b ≤ a` using positivity of `b`. -/
theorem div_le_self_pos (a b : Nat) (hb : 0 < b) : a / b ≤ a := by
  have h1 : a / b ≤ a / b * b := Nat.le_mul_of_pos_right (a / b) hb
  exact Nat.le_trans h1 (div_mul_le_self a b)

/-- `c^(n+1) / c^n = c` for `c ≥ 1`.  ∅-axiom. -/
theorem pow_succ_div (c n : Nat) (hc : 1 ≤ c) : c ^ (n + 1) / c ^ n = c := by
  rw [Nat.pow_succ]
  exact mul_div_cancel_left_pure (c ^ n) c (Nat.pos_pow_of_pos n hc)

/-- `2x ≤ 2y → x ≤ y`, ∅-axiom (left-cancel a positive factor). -/
theorem two_cancel (x y : Nat) (h : 2 * x ≤ 2 * y) : x ≤ y :=
  Nat.le_of_mul_le_mul_left h (by decide)

/-- `2x < 2y → x < y`, ∅-axiom (Lean-core `Nat.lt_of_mul_lt_mul_left`
    pulls `Classical`; rule out `y ≤ x` via `Nat.mul_le_mul_left`). -/
theorem two_cancel_lt (x y : Nat) (h : 2 * x < 2 * y) : x < y := by
  cases Nat.lt_or_ge x y with
  | inl hlt => exact hlt
  | inr hge => exact (Nat.not_lt.mpr (Nat.mul_le_mul_left 2 hge) h).elim

end E213.Meta.Nat.NatDiv213
