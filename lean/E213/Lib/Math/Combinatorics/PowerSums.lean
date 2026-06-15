import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# Power-sum / figurate identities (∅-axiom)

The classical closed-form power sums, all genuinely absent from the corpus (the
existing triangular maps `tri`/`T n = n(n+1)/2` use division; these are the
exact cross-multiplied / square forms):

  * **Gauss sum** `2·(0+1+…+n) = n(n+1)` (`gauss_sum`).
  * **Sum of odd numbers** `1+3+…+(2n−1) = n²` (`sum_odd`).
  * **Sum of squares** `6·Σ_{i≤n} i² = n(n+1)(2n+1)` (`sum_squares`).
  * ★ **Nicomachus's theorem** `Σ_{i≤n} i³ = (Σ_{i≤n} i)²` (`nicomachus`) — the
    sum of cubes is the square of the sum (both `×4` reduce to `n²(n+1)²`).

All cross-multiplied to stay subtraction-free; clean inductions on the `sumTo`
recurrence closed by `ring_nat`.  Nicomachus cancels the common factor `4` via
`Nat.eq_of_mul_eq_mul_left`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.PowerSums

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)

/-- **Gauss sum**, cross-multiplied: `2·(0+1+…+n) = n(n+1)`. -/
theorem gauss_sum (n : Nat) : 2 * sumTo (n + 1) (fun i => i) = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ]
    have h : 2 * (sumTo (k + 1) (fun i => i) + (k + 1))
        = 2 * sumTo (k + 1) (fun i => i) + 2 * (k + 1) := by ring_nat
    rw [h, ih]
    ring_nat

/-- **Sum of odd numbers**: `1+3+…+(2n−1) = n²`. -/
theorem sum_odd (n : Nat) : sumTo n (fun i => 2 * i + 1) = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ, ih]
    ring_nat

/-- **Sum of squares**, cross-multiplied: `6·Σi² = n(n+1)(2n+1)`. -/
theorem sum_squares (n : Nat) :
    6 * sumTo (n + 1) (fun i => i * i) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ]
    have h : 6 * (sumTo (k + 1) (fun i => i * i) + (k + 1) * (k + 1))
        = 6 * sumTo (k + 1) (fun i => i * i) + 6 * ((k + 1) * (k + 1)) := by ring_nat
    rw [h, ih]
    ring_nat

/-- Closed form `4·(Σi)² = n²(n+1)²` — squared Gauss, helper for Nicomachus. -/
theorem four_sum_sq (n : Nat) :
    4 * (sumTo (n + 1) (fun i => i) * sumTo (n + 1) (fun i => i))
      = n * n * ((n + 1) * (n + 1)) := by
  have hg := gauss_sum n
  have h4 : 4 * (sumTo (n + 1) (fun i => i) * sumTo (n + 1) (fun i => i))
      = (2 * sumTo (n + 1) (fun i => i)) * (2 * sumTo (n + 1) (fun i => i)) := by ring_nat
  rw [h4, hg]
  ring_nat

/-- Closed form `4·Σi³ = n²(n+1)²`. -/
theorem four_sum_cubes (n : Nat) :
    4 * sumTo (n + 1) (fun i => i * i * i) = n * n * ((n + 1) * (n + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ]
    have h : 4 * (sumTo (k + 1) (fun i => i * i * i) + (k + 1) * (k + 1) * (k + 1))
        = 4 * sumTo (k + 1) (fun i => i * i * i)
          + 4 * ((k + 1) * (k + 1) * (k + 1)) := by ring_nat
    rw [h, ih]
    ring_nat

/-- ★ **Nicomachus's theorem**: `Σ_{i≤n} i³ = (Σ_{i≤n} i)²`.
    Both sides `×4` reduce to `n²(n+1)²`, so they agree; cancel the factor `4`. -/
theorem nicomachus (n : Nat) :
    sumTo (n + 1) (fun i => i * i * i)
      = sumTo (n + 1) (fun i => i) * sumTo (n + 1) (fun i => i) := by
  have h1 := four_sum_cubes n
  have h2 := four_sum_sq n
  have heq : 4 * sumTo (n + 1) (fun i => i * i * i)
      = 4 * (sumTo (n + 1) (fun i => i) * sumTo (n + 1) (fun i => i)) := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_left (by decide) heq

/-- Smoke: `1+3+5+7+9 = 25 = 5²`, and Nicomachus on `n = 3` (`0³+1³+2³+3³ = 36 = 6²`). -/
theorem powersums_smoke :
    sumTo 5 (fun i => 2 * i + 1) = 25
    ∧ sumTo 4 (fun i => i * i * i) = sumTo 4 (fun i => i) * sumTo 4 (fun i => i) := by
  refine ⟨by decide, by decide⟩

/-! ## Faulhaber, continued: fourth and fifth powers

The textbook forms `30·Σi⁴ = n(n+1)(2n+1)(3n²+3n−1)` and
`12·Σi⁵ = n²(n+1)²(2n²+2n−1)` carry a `−1` that would force Nat truncated
subtraction; the equivalent fully-expanded *additive* forms (the `−n`/`−n²`
moved to the left) keep `ring_nat` happy. -/

/-- ★ **Sum of fourth powers** (Faulhaber k=4): `30·Σ_{i≤n} i⁴ + n = 6n⁵+15n⁴+10n³`
    (≡ `30·Σi⁴ = n(n+1)(2n+1)(3n²+3n−1)`). -/
theorem sum_fourth (n : Nat) :
    30 * sumTo (n + 1) (fun i => i * i * i * i) + n
      = 6 * (n * n * n * n * n) + 15 * (n * n * n * n) + 10 * (n * n * n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ]
    have h : 30 * (sumTo (k + 1) (fun i => i * i * i * i)
          + (k + 1) * (k + 1) * (k + 1) * (k + 1)) + (k + 1)
        = (30 * sumTo (k + 1) (fun i => i * i * i * i) + k)
          + (30 * ((k + 1) * (k + 1) * (k + 1) * (k + 1)) + 1) := by ring_nat
    rw [h, ih]
    ring_nat

/-- ★ **Sum of fifth powers** (Faulhaber k=5): `12·Σ_{i≤n} i⁵ + n² = 2n⁶+6n⁵+5n⁴`
    (≡ `12·Σi⁵ = n²(n+1)²(2n²+2n−1)`). -/
theorem sum_fifth (n : Nat) :
    12 * sumTo (n + 1) (fun i => i * i * i * i * i) + n * n
      = 2 * (n * n * n * n * n * n) + 6 * (n * n * n * n * n)
        + 5 * (n * n * n * n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo_succ]
    have h : 12 * (sumTo (k + 1) (fun i => i * i * i * i * i)
          + (k + 1) * (k + 1) * (k + 1) * (k + 1) * (k + 1)) + (k + 1) * (k + 1)
        = (12 * sumTo (k + 1) (fun i => i * i * i * i * i) + k * k)
          + (12 * ((k + 1) * (k + 1) * (k + 1) * (k + 1) * (k + 1))
            + (2 * k + 1)) := by ring_nat
    rw [h, ih]
    ring_nat

end E213.Lib.Math.Combinatorics.PowerSums
