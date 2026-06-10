import E213.Meta.Int213.Order

/-!
# OrderMul — pure `Int` multiplicative order lemmas

The Lean-core multiplicative order lemmas (`Int.mul_le_mul_of_nonneg_left`,
`Int.lt_irrefl`, `Int.lt_or_le`) are `propext`-dirty.  This module supplies the `∅`-axiom
replacements needed for the Eisenstein Euclidean descent: right-multiplication monotonicity,
the sign trichotomy, nonneg·nonpos, and strict positivity of a product.

All zero-axiom.
-/

namespace E213.Meta.Int213.OrderMul

open E213.Meta.Int213 (mul_nonneg sub_mul mul_neg mul_comm mul_one)
open E213.Meta.Int213.Order
  (le_of_sub_nonneg sub_nonneg_of_le le_zero_of_nonneg nonneg_of_le_zero
   lt_of_sub_one_nonneg zero_sub ofNat_succ_sub_one le_of_lt lt_of_lt_of_le lt_of_le_of_lt)

/-- ★★ **Right-multiplication is monotone for a nonnegative factor.** -/
theorem mul_le_mul_right_nonneg {a b : Int} (hab : a ≤ b) (c : Int) (hc : 0 ≤ c) :
    a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) := le_zero_of_nonneg (sub_nonneg_of_le hab)
  have h2 : 0 ≤ (b - a) * c := mul_nonneg h1 hc
  rw [sub_mul] at h2
  exact le_of_sub_nonneg (nonneg_of_le_zero h2)

/-- ★★ **Left-multiplication is monotone for a nonnegative factor.** -/
theorem mul_le_mul_left_nonneg {a b : Int} (hab : a ≤ b) (c : Int) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_right_nonneg hab c hc

/-- ★★★ **The integer sign trichotomy** (`∅`-axiom, by constructor cases): every integer is
    `≥ 0` or `< 0`. -/
theorem int_sign : ∀ x : Int, 0 ≤ x ∨ x < 0
  | Int.ofNat n => Or.inl (Int.ofNat_nonneg n)
  | Int.negSucc n => Or.inr <| by
      apply lt_of_sub_one_nonneg
      have hval : (0 : Int) - Int.negSucc n - 1 = Int.ofNat n := by
        rw [zero_sub, Int.neg_negSucc]; exact ofNat_succ_sub_one n
      rw [hval]
      exact ⟨n⟩

/-- ★★ **Nonneg times nonpos is nonpos.** -/
theorem mul_nonpos_of_nonneg_of_nonpos {a b : Int} (ha : 0 ≤ a) (hb : b ≤ 0) :
    a * b ≤ 0 := by
  have hnb : 0 ≤ -b := le_zero_of_nonneg (zero_sub b ▸ sub_nonneg_of_le hb)
  have h : 0 ≤ a * (-b) := mul_nonneg ha hnb
  rw [mul_neg] at h
  -- 0 ≤ -(a*b) ⟹ a*b ≤ 0
  exact le_of_sub_nonneg (nonneg_of_le_zero (zero_sub (a * b) ▸ h))

/-! ## §2 — `ℕ → ℤ` cast lemmas (pure replacements for `propext`-dirty core) -/

/-- ★★ **Monotone `ℕ → ℤ` cast** (`Int.ofNat_le` is `propext`-dirty). -/
theorem ofNat_le_of_le {a b : Nat} (h : a ≤ b) : (a : Int) ≤ (b : Int) := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  have hsub : (b : Int) - (a : Int) = (k : Int) := by
    rw [← hk, Int.ofNat_add]; ring_intZ
  refine le_of_sub_nonneg ?_
  rw [hsub]; exact ⟨k⟩

/-- ★★ **`↑|N| = N` for `N ≥ 0`** (`Int.natAbs_of_nonneg` is `propext`-dirty). -/
theorem natAbs_cast_of_nonneg {N : Int} (h : 0 ≤ N) : (N.natAbs : Int) = N := by
  cases N with
  | ofNat n => rfl
  | negSucc n => exact absurd h (by intro hc; cases hc)

/-! ## §3 — strict positivity of a product, and irreflexivity -/

/-- ★★ **Product of positives is positive** (`Int.mul_pos` is `propext`-dirty). -/
theorem mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h1a : (1 : Int) ≤ a := ha
  have hb0 : (0 : Int) ≤ b := le_of_lt hb
  have hble : b ≤ a * b := by
    have hx := mul_le_mul_right_nonneg h1a b hb0
    rwa [mul_comm 1 b, mul_one] at hx
  exact lt_of_lt_of_le hb hble

/-- ★★ **Positive right-cancellation**: `a·c ≤ b·c` and `0 < c` ⟹ `a ≤ b`.  The converse of
    `mul_le_mul_right_nonneg` — if `b < a` then `(a−b)·c > 0`, so `b·c < a·c`, contradicting
    the hypothesis. -/
theorem le_of_mul_le_mul_right_pos {a b c : Int} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  apply Order.le_of_sub_nonneg
  apply Order.nonneg_of_le_zero
  rcases Order.pos_zero_or_neg (b - a) with hpos | hzero | hneg
  · exact Order.le_of_lt hpos
  · rw [hzero]; exact Order.le_refl 0
  · exfalso
    have ha_b : (0 : Int) < a - b := by
      rw [show a - b = -(b - a) from by ring_intZ]; exact Order.neg_pos_of_neg hneg
    have hlt : b * c < a * c := by
      apply Order.lt_of_sub_pos
      rw [show a * c - b * c = (a - b) * c from by ring_intZ]
      exact mul_pos ha_b hc
    exact Order.not_le_of_lt hlt h

/-- ★★ **Doubling cancellation at zero**: `2·a = 0 ⟹ a = 0`, both `≤`-directions via
    `le_of_mul_le_mul_right_pos`.  The closing step of any antisymmetric-kernel sum
    (`S = −S ⟹ S = 0`) without division. -/
theorem eq_zero_of_two_mul_eq_zero {a : Int} (h : 2 * a = 0) : a = 0 := by
  have hle : a ≤ 0 := le_of_mul_le_mul_right_pos (c := 2)
    (by rw [mul_comm a 2, h, E213.Meta.Int213.zero_mul]; exact Order.le_refl 0) (by decide)
  have hge : (0 : Int) ≤ a := le_of_mul_le_mul_right_pos (c := 2)
    (by rw [E213.Meta.Int213.zero_mul, mul_comm a 2, h]; exact Order.le_refl 0) (by decide)
  exact Order.le_antisymm hle hge

/-- ★★ **`<` is irreflexive** (`Int.lt_irrefl` is `propext`-dirty), by reducing `a < a` to
    `(-1).NonNeg`. -/
theorem int_lt_irrefl (a : Int) : ¬ (a < a) := by
  intro h
  have hnn : (a - (a + 1)).NonNeg := h
  rw [show a - (a + 1) = -1 from by ring_intZ] at hnn
  cases hnn

/-- ★★ **`natAbs` is strictly monotone on nonnegatives**: `0 ≤ a`, `a < b` ⟹
    `a.natAbs < b.natAbs` — the fuel-decrease for the `ℤ[ω]` Euclidean recursion. -/
theorem natAbs_lt_of_lt {a b : Int} (ha : 0 ≤ a) (hab : a < b) : a.natAbs < b.natAbs := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rcases Nat.lt_or_ge a.natAbs b.natAbs with h | h
  · exact h
  · exfalso
    have h1 : (b.natAbs : Int) ≤ (a.natAbs : Int) := ofNat_le_of_le h
    rw [natAbs_cast_of_nonneg ha, natAbs_cast_of_nonneg hb] at h1
    exact int_lt_irrefl a (lt_of_lt_of_le hab h1)

end E213.Meta.Int213.OrderMul
