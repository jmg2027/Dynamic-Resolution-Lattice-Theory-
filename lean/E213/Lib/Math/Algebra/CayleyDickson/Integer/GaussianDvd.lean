import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep

/-!
# GaussianDvd — divisibility and the norm in `ℤ[i]` (Gaussian Phase 2)

The disc-`−4` analog of `EisensteinDvd`: the bridge between `ℤ[i]`-divisibility and the
integer norm needed for the split-prime descent.

  * `mul_conj_self` — `u · conj u = ofInt ‖u‖²`.
  * ★★★ `normSq_dvd_of_dvd` — `a ∣ b` ⟹ `‖a‖² ∣ ‖b‖²`.
  * ★★★ `unit_of_normSq_one` / `normSq_one_of_unit` — `unit ⟺ ‖·‖² = 1`.
  * `dvd_components_of_dvd` — `ofInt p ∣ θ` ⟹ `p ∣ θ.re ∧ p ∣ θ.im`.
  * `normSq_x_sub_i` — `‖x − i‖² = x² + 1`.
  * `not_dvd_x_sub_i` — a non-unit `p` does not divide `x − i` (its `im` is the unit `−1`).

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDvd

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI

/-- `u · conj u = ofInt ‖u‖²` (the norm realised as a ring element). -/
theorem mul_conj_self (u : ZI) : u * ZI.conj u = ZI.ofInt u.normSq := by
  cases u with
  | mk p q =>
    refine ZI.ext ?_ ?_
    · show p * p - q * (-q) = p * p + q * q
      ring_intZ
    · show p * (-q) + q * p = 0
      have hz : p * (-q) + q * p = q * q - q * q := by ring_intZ
      rw [hz, E213.Meta.Int213.Order.sub_self_zero]

/-- ★★★ **The norm respects divisibility.**  `b = a · c` ⟹ `‖a‖² ∣ ‖b‖²`. -/
theorem normSq_dvd_of_dvd (a b c : ZI) (hc : b = a * c) : a.normSq ∣ b.normSq := by
  rw [hc, normSq_mul]
  exact ⟨c.normSq, rfl⟩

/-- ★★★ **A norm-1 element is a unit.**  `‖u‖² = 1 ⟹ u · conj u = ofInt 1`. -/
theorem unit_of_normSq_one (u : ZI) (h : u.normSq = 1) : u * ZI.conj u = ZI.ofInt 1 := by
  rw [mul_conj_self, h]

/-- `n·m = 1` over `ℕ` forces `n = 1`. -/
private theorem nat_eq_one_of_mul (n m : Nat) (h : n * m = 1) : n = 1 := by
  cases n with
  | zero => rw [Nat.zero_mul] at h; exact absurd h (by decide)
  | succ k =>
    cases k with
    | zero => rfl
    | succ j =>
      exfalso
      cases m with
      | zero => rw [Nat.mul_zero] at h; exact absurd h (by decide)
      | succ i =>
        have h2 : 2 ≤ (j + 2) * (i + 1) :=
          Nat.le_trans (by decide : 2 ≤ 2 * 1)
            (Nat.mul_le_mul (Nat.le_add_left 2 j) (Nat.succ_le_succ (Nat.zero_le i)))
        rw [h] at h2; exact absurd h2 (by decide)

/-- `a·b = 1` with `a, b ≥ 0` forces `a = 1`. -/
private theorem int_mul_eq_one_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a * b = 1) : a = 1 := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m =>
      have hnm : n * m = 1 := Int.ofNat.inj ((Int.ofNat_mul n m).trans h)
      rw [nat_eq_one_of_mul n m hnm]; rfl
    | negSucc m => exact absurd hb (by intro hc; cases hc)
  | negSucc n => exact absurd ha (by intro hc; cases hc)

/-- ★★★ **A unit has norm 1.**  `u · v = ofInt 1 ⟹ ‖u‖² = 1`. -/
theorem normSq_one_of_unit (u v : ZI) (h : u * v = ZI.ofInt 1) : u.normSq = 1 := by
  have hn : u.normSq * v.normSq = 1 := by rw [← normSq_mul, h]; rfl
  exact int_mul_eq_one_nonneg (normSq_nonneg u) (normSq_nonneg v) hn

/-! ## §2 — the descent setup -/

/-- **`ofInt p ∣ θ` forces `p` to divide both coordinates.** -/
theorem dvd_components_of_dvd (p : Int) (θ c : ZI) (h : θ = ZI.ofInt p * c) :
    (p ∣ θ.re) ∧ (p ∣ θ.im) := by
  have hre : θ.re = p * c.re := by
    rw [h]
    show p * c.re - 0 * c.im = p * c.re
    rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.Order.sub_zero]
  have him : θ.im = p * c.im := by
    rw [h]
    show p * c.im + 0 * c.re = p * c.im
    rw [E213.Meta.Int213.zero_mul, Int.add_zero]
  exact ⟨⟨c.re, hre⟩, ⟨c.im, him⟩⟩

/-- `‖x − i‖² = x² + 1` (the cyclotomic value `p` divides when `x² ≡ −1 mod p`). -/
theorem normSq_x_sub_i (x : Int) : (⟨x, -1⟩ : ZI).normSq = x * x + 1 := by
  show x * x + (-1) * (-1) = x * x + 1
  ring_intZ

/-- ★★★ **`p` (a non-unit of `ℤ`) does not divide `x − i`.**  Its imaginary part is the unit
    `−1`, so `ofInt p ∣ ⟨x,−1⟩` would give `p ∣ −1`, hence `p ∣ 1`. -/
theorem not_dvd_x_sub_i (p x : Int) (hp : ¬ (p ∣ (1 : Int))) :
    ¬ ∃ c : ZI, (⟨x, -1⟩ : ZI) = ZI.ofInt p * c := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hpm1 : p ∣ (-1 : Int) := (dvd_components_of_dvd p ⟨x, -1⟩ c hc).2
  obtain ⟨k, hk⟩ := hpm1
  have h1 : (1 : Int) = p * (-k) := by rw [E213.Meta.Int213.mul_neg, ← hk, Int.neg_neg]
  exact hp ⟨-k, h1⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDvd
