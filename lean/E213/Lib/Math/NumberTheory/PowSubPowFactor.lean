import E213.Lib.Math.NumberTheory.GeometricSeries

/-!
# Homogeneous factorization `aⁿ⁺¹ − bⁿ⁺¹ = (a − b)·Σ aⁱbⁿ⁻ⁱ` (∅-axiom)

The two-variable (homogeneous) strengthening of the geometric series: `DiffPowDvd` proves only the
*divisibility* `(a−b) ∣ (aⁿ−bⁿ)` (via an opaque witness); this file gives the **explicit quotient**

> `aⁿ⁺¹ − bⁿ⁺¹ = (a − b) · Σ_{i=0}^{n} aⁱ·bⁿ⁻ⁱ`.

This is the cyclotomic-factorization heart (`a−b ∣ aⁿ−bⁿ`, the cofactor `Σ aⁱbⁿ⁻ⁱ` is the
`n`-th complete homogeneous symmetric polynomial in `{a,b}`) and the algebraic foundation of the
lifting-the-exponent lemma.  Setting `b = 1` recovers `GeometricSeries.geom_sum`.

The cofactor is captured by the recursion `geomTwo a b (n+1) = a·geomTwo a b n + bⁿ⁺¹` (avoiding the
awkward `n−i` exponent), so the whole proof is two `ring_intZ` steps.  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PowSubPowFactor

open E213.Lib.Math.NumberTheory.DiffPowDvd (ipow ipow_zero ipow_succ)

/-- The cofactor `Σ_{i=0}^{n} aⁱ·bⁿ⁻ⁱ`, via the `n`-recursion `S(n+1) = a·S(n) + bⁿ⁺¹`
    (= the `n`-th complete homogeneous symmetric polynomial in `a, b`). -/
def geomTwo (a b : Int) : Nat → Int
  | 0     => 1
  | n + 1 => a * geomTwo a b n + ipow b (n + 1)

@[simp] theorem geomTwo_zero (a b : Int) : geomTwo a b 0 = 1 := rfl
theorem geomTwo_succ (a b : Int) (n : Nat) :
    geomTwo a b (n + 1) = a * geomTwo a b n + ipow b (n + 1) := rfl

/-- ★★★ **Homogeneous power-difference factorization**:
    `aⁿ⁺¹ − bⁿ⁺¹ = (a − b) · Σ_{i=0}^{n} aⁱ·bⁿ⁻ⁱ`.  Induction on `n` via the `geomTwo` recursion. -/
theorem pow_sub_pow_factor (a b : Int) :
    ∀ n, ipow a (n + 1) - ipow b (n + 1) = (a - b) * geomTwo a b n
  | 0 => by
      show ipow a 1 - ipow b 1 = (a - b) * 1
      show ipow a 0 * a - ipow b 0 * b = (a - b) * 1
      show (1 : Int) * a - 1 * b = (a - b) * 1
      ring_intZ
  | n + 1 => by
      rw [geomTwo_succ]
      -- `(a-b)·(a·S(n) + b^{n+1}) = a·((a-b)·S(n)) + (a-b)·b^{n+1}`, fold IH, then ring
      have ih := pow_sub_pow_factor a b n
      rw [ipow_succ a (n + 1), ipow_succ b (n + 1)]
      -- goal: a^{n+1}·a − b^{n+1}·b = (a−b)·(a·S(n) + b^{n+1})
      have key : (a - b) * (a * geomTwo a b n + ipow b (n + 1))
          = a * ((a - b) * geomTwo a b n) + (a - b) * ipow b (n + 1) := by ring_intZ
      rw [key, ← ih]
      -- goal: a^{n+1}·a − b^{n+1}·b = a·(a^{n+1} − b^{n+1}) + (a−b)·b^{n+1}
      ring_intZ

/-- `1ⁿ = 1` for the local `ipow`. -/
theorem one_pow_ipow : ∀ k, ipow (1 : Int) k = 1
  | 0     => rfl
  | k + 1 => by rw [ipow_succ, one_pow_ipow k]; show (1 : Int) * 1 = 1; decide

/-- `b = 1` recovers the classic `(a − 1) ∣ (aⁿ⁺¹ − 1)` cofactor form. -/
theorem pow_sub_one_factor (a : Int) (n : Nat) :
    ipow a (n + 1) - 1 = (a - 1) * geomTwo a 1 n := by
  have h := pow_sub_pow_factor a 1 n
  rw [one_pow_ipow (n + 1)] at h
  exact h

/-- Smoke: `2⁴ − 1⁴ = 15 = (2−1)·(8+4+2+1)`; `3³ − 2³ = 19 = (3−2)·(9+6+4)`. -/
theorem pow_sub_pow_smoke :
    ipow 2 4 - ipow 1 4 = (2 - 1) * geomTwo 2 1 3
    ∧ ipow 3 3 - ipow 2 3 = (3 - 2) * geomTwo 3 2 2 := by decide

end E213.Lib.Math.NumberTheory.PowSubPowFactor
