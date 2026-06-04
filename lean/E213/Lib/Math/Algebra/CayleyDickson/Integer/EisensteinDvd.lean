import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep

/-!
# EisensteinDvd — divisibility and the norm in `ℤ[ω]` (Phase 2 of the descent)

With `ℤ[ω]` norm-Euclidean (`EisensteinDivStep.zomega_div_step`), the split-prime descent
needs the bridge between `ℤ[ω]`-divisibility and the integer norm:

  * ★★★ `normSq_dvd_of_dvd` — `a ∣ b` in `ℤ[ω]` ⟹ `‖a‖² ∣ ‖b‖²` in `ℤ` (the norm is
    multiplicative, so a factor's norm divides the product's norm — the workhorse that turns
    a proper `ℤ[ω]`-factor of `p` into a proper integer factor of `p²`).
  * ★★★ `unit_of_normSq_one` — `‖u‖² = 1 ⟹ u · conj u = 1`: a norm-1 element is a **unit**,
    with explicit inverse `conj u` (immediate from `mul_conj_self`).  The clean half of
    "unit ⟺ norm 1".

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)

/-- ★★★ **The norm respects divisibility.**  If `b = a · c` in `ℤ[ω]`, then `‖a‖² ∣ ‖b‖²`
    in `ℤ` (via `‖b‖² = ‖a‖²·‖c‖²`). -/
theorem normSq_dvd_of_dvd (a b c : ZOmega) (hc : b = a * c) :
    a.normSq ∣ b.normSq := by
  rw [hc, normSq_mul]
  exact ⟨c.normSq, rfl⟩

/-- ★★★ **A norm-1 element is a unit.**  `‖u‖² = 1 ⟹ u · conj u = ofInt 1` — the conjugate
    is the explicit inverse (from `mul_conj_self : u · conj u = ofInt ‖u‖²`). -/
theorem unit_of_normSq_one (u : ZOmega) (h : u.normSq = 1) :
    u * u.conj = ZOmega.ofInt 1 := by
  rw [mul_conj_self, h]

/-- `n·m = 1` over `ℕ` forces `n = 1` (`0` undershoots, `≥ 2` overshoots). -/
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

/-- `a·b = 1` with `a, b ≥ 0` forces `a = 1` (over `ℤ`, via `natAbs`-free `ofNat` cases). -/
private theorem int_mul_eq_one_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a * b = 1) : a = 1 := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m =>
      have hnm : n * m = 1 :=
        Int.ofNat.inj ((Int.ofNat_mul n m).trans h)
      rw [nat_eq_one_of_mul n m hnm]; rfl
    | negSucc m => exact absurd hb (by intro hc; cases hc)
  | negSucc n => exact absurd ha (by intro hc; cases hc)

/-- ★★★ **A unit has norm 1.**  `u · v = ofInt 1 ⟹ ‖u‖² = 1` (the multiplicative norm forces
    `‖u‖²·‖v‖² = 1`, and both are nonnegative).  With `unit_of_normSq_one` this is the full
    `unit ⟺ norm 1`, so a norm-`p` element (`p` prime) is never a unit. -/
theorem normSq_one_of_unit (u v : ZOmega) (h : u * v = ZOmega.ofInt 1) :
    u.normSq = 1 := by
  have hn : u.normSq * v.normSq = 1 := by rw [← normSq_mul, h]; rfl
  exact int_mul_eq_one_nonneg (normSq_nonneg u) (normSq_nonneg v) hn

/-! ## §2 — the descent setup: `p ∣ θ` forces `p` to divide both coordinates -/

/-- ★★★ **`ofInt p ∣ θ` forces `p` to divide both coordinates.**  `ofInt p · c = ⟨p·c.re,
    p·c.im⟩`, so `p ∣ θ.re` and `p ∣ θ.im` in `ℤ`. -/
theorem dvd_components_of_dvd (p : Int) (θ c : ZOmega) (h : θ = ZOmega.ofInt p * c) :
    (p ∣ θ.re) ∧ (p ∣ θ.im) := by
  have hre : θ.re = p * c.re := by
    rw [h]
    show p * c.re - 0 * c.im = p * c.re
    rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.Order.sub_zero]
  have him : θ.im = p * c.im := by
    rw [h]
    show p * c.im + 0 * c.re - 0 * c.im = p * c.im
    rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul,
        E213.Meta.Int213.Order.sub_zero, E213.Meta.Int213.add_comm,
        E213.Meta.Int213.zero_add]
  exact ⟨⟨c.re, hre⟩, ⟨c.im, him⟩⟩

/-- The element `x − ω = ⟨x, −1⟩` has norm `x² + x + 1` (the cyclotomic value `p` divides
    when `x` is a primitive cube root mod `p`). -/
theorem normSq_x_sub_omega (x : Int) : (⟨x, -1⟩ : ZOmega).normSq = x * x + x + 1 := by
  show x * x - x * (-1) + (-1) * (-1) = x * x + x + 1
  ring_intZ

/-- ★★★ **`p` (a non-unit of `ℤ`) does not divide `x − ω`.**  Its imaginary part is the unit
    `−1`, so `ofInt p ∣ ⟨x,−1⟩` would give `p ∣ −1`, hence `p ∣ 1` — excluded for a prime.
    (Takes `¬ p ∣ 1` — true for any prime — as hypothesis, sidestepping the `propext`-dirty
    `Int.le_of_dvd`.) -/
theorem not_dvd_x_sub_omega (p x : Int) (hp : ¬ (p ∣ (1 : Int))) :
    ¬ ∃ c : ZOmega, (⟨x, -1⟩ : ZOmega) = ZOmega.ofInt p * c := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hpm1 : p ∣ (-1 : Int) := (dvd_components_of_dvd p ⟨x, -1⟩ c hc).2
  obtain ⟨k, hk⟩ := hpm1
  have h1 : (1 : Int) = p * (-k) := by rw [E213.Meta.Int213.mul_neg, ← hk, Int.neg_neg]
  exact hp ⟨-k, h1⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
