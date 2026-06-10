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

/-- `(a + b * c) / b = a / b + c` (`0 < b`).  ∅-axiom replacement for
    Lean-core `Nat.add_mul_div_left` (which pulls `propext`).  Induction
    on `c` via `add_div_right_pos`. -/
theorem add_mul_div_left_pure (a b c : Nat) (h : 0 < b) :
    (a + b * c) / b = a / b + c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, add_div_right_pos h, ih]
    exact Nat.add_assoc (a / b) k 1

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

/-- `0 % a = 0`, ∅-axiom (Lean-core `Nat.zero_mod` brings `propext`). -/
theorem zero_mod_pure (a : Nat) : 0 % a = 0 := by
  rw [Nat.mod_eq]
  rw [if_neg (fun h : 0 < a ∧ a ≤ 0 =>
    Nat.not_succ_le_zero 0 (Nat.le_trans h.1 h.2))]

/-- `a * x % a = 0`, ∅-axiom replacement for `Nat.mul_mod_right`. -/
theorem mul_mod_self_pure (a : Nat) : ∀ (x : Nat), a * x % a = 0
  | 0 => by rw [Nat.mul_zero]; exact zero_mod_pure a
  | x + 1 => by
    cases a with
    | zero => rw [Nat.zero_mul]
    | succ k =>
      rw [Nat.mul_succ]
      rw [add_mod_right_pos (Nat.succ_pos k)]
      exact mul_mod_self_pure (k + 1) x

/-- `a * (b / a) + b % a = b`, ∅-axiom replacement for
    `Nat.div_add_mod` (Lean-core brings `propext`).  Strong recursion
    on `b`, same shape as `div_mul_le_self`. -/
theorem div_add_mod_pure : ∀ (b a : Nat), a * (b / a) + b % a = b := fun b a =>
  Nat.strongRecOn b (motive := fun b => a * (b / a) + b % a = b) fun b ih => by
    show a * (b / a) + b % a = b
    by_cases h : 0 < a ∧ a ≤ b
    · have hsub_lt : b - a < b := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
      have ih' := ih (b - a) hsub_lt
      have hd : b / a = (b - a) / a + 1 := by rw [Nat.div_eq]; rw [if_pos h]
      have hm : b % a = (b - a) % a := by rw [Nat.mod_eq]; rw [if_pos h]
      rw [hd, hm, Nat.mul_succ, Nat.add_right_comm, ih']
      exact sub_add_cancel h.2
    · have hd : b / a = 0 := by rw [Nat.div_eq]; rw [if_neg h]
      have hm : b % a = b := by rw [Nat.mod_eq]; rw [if_neg h]
      rw [hd, hm, Nat.mul_zero, Nat.zero_add]

/-! ## Witness location — the ÷-sandwich

The ×-mirror of `Meta/Int213/Core.lean`'s witness characterization.
The question `a * x = b` may have no ℕ-witness, but the sandwich
`a * x ≤ b < a * (x + 1)` always pins exactly one location
(`div_sandwich`, `div_sandwich_unique`), and that location is `b / a`
(`div_eq_of_sandwich`).  Unlike the `+`-sandwich, which collapses to a
point (`Int213.eq_of_sandwich`), the ÷-sandwich keeps an interval of
`a - 1` missed rungs; the exact witness exists precisely when the
remainder readout vanishes (`mul_witness_iff_mod_eq_zero`). -/

/-- The ÷-sandwich always locates: `a * (b / a) ≤ b < a * (b / a + 1)`
    when `0 < a`.  Division is the located — not necessarily witnessed —
    answer to the ×-question. -/
theorem div_sandwich (a b : Nat) (ha : 0 < a) :
    a * (b / a) ≤ b ∧ b < a * (b / a + 1) := by
  constructor
  · rw [Nat.mul_comm]
    exact div_mul_le_self b a
  · have hmod : a * (b / a) + b % a = b := div_add_mod_pure b a
    have hlt : b % a < a := Nat.mod_lt b ha
    have h2 : a * (b / a) + b % a < a * (b / a) + a :=
      Nat.add_lt_add_left hlt _
    rw [hmod] at h2
    rw [Nat.mul_succ]
    exact h2

/-- The ÷-sandwich pins at most one location. -/
theorem div_sandwich_unique {a b x y : Nat}
    (hx1 : a * x ≤ b) (hx2 : b < a * (x + 1))
    (hy1 : a * y ≤ b) (hy2 : b < a * (y + 1)) : x = y := by
  have hxy : x < y + 1 := by
    cases Nat.lt_or_ge x (y + 1) with
    | inl h => exact h
    | inr h =>
        exact (Nat.not_lt.mpr
          (Nat.le_trans (Nat.mul_le_mul_left a h) hx1) hy2).elim
  have hyx : y < x + 1 := by
    cases Nat.lt_or_ge y (x + 1) with
    | inl h => exact h
    | inr h =>
        exact (Nat.not_lt.mpr
          (Nat.le_trans (Nat.mul_le_mul_left a h) hy1) hx2).elim
  exact Nat.le_antisymm (Nat.le_of_lt_succ hxy) (Nat.le_of_lt_succ hyx)

/-- The sandwich presentation reads out through the division-Lens:
    the inequality pair determines `x = b / a`.  ÷-mirror of
    `Int213.subNatNat_of_sandwich`. -/
theorem div_eq_of_sandwich {a b x : Nat} (ha : 0 < a)
    (h1 : a * x ≤ b) (h2 : b < a * (x + 1)) : x = b / a :=
  div_sandwich_unique h1 h2 (div_sandwich a b ha).1 (div_sandwich a b ha).2

/-- Exact ×-witness iff the remainder readout vanishes: the ÷-question's
    interval collapses to a witnessed point only on the multiples of `a`.
    ÷-mirror of `Int213.witness_total`/`witness_not_both`, with the
    two-valued swap readout (sign) replaced by the `a`-valued position
    readout (remainder). -/
theorem mul_witness_iff_mod_eq_zero (a b : Nat) :
    (∃ x, a * x = b) ↔ b % a = 0 := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    rw [← hx]
    exact mul_mod_self_pure a x
  · intro h
    refine ⟨b / a, ?_⟩
    have hmod : a * (b / a) + b % a = b := div_add_mod_pure b a
    rw [h, Nat.add_zero] at hmod
    exact hmod

end E213.Meta.Nat.NatDiv213
