import E213.Lib.Math.NumberTheory.EulerTotient

/-!
# Sum-of-divisors σ + divisor-count τ (∅-axiom)

Companion to `EulerTotient.lean` / `MobiusFunction.lean`.  Reuses the template's
propext-free `divisorSum` (`Bool.toNat` indicator `dvdInd`):

  * `sigma n` = `Σ_{d ∣ n} d`   (sum of divisors).
  * `tau n`   = `Σ_{d ∣ n} 1`   (number of divisors).
  * ★ `perfect_table` — the perfect-number condition `σ(n) = 2n` at n = 6, 28
    (with non-perfect counterexamples).

All declarations PURE (compose only `divisorSum`/`dvdInd`/`sumTo`); tables close
by `decide`.  General multiplicativity (σ, τ multiplicative) is proven via the
partition-by-divisor toolkit (`DivisorMultiplicative`).
The corpus had no σ/τ as arithmetic functions (the `sigma` elsewhere is a variable
name / Gram matrix).
-/

namespace E213.Lib.Math.NumberTheory.SumOfDivisors

open E213.Lib.Math.NumberTheory.EulerTotient (divisorSum)

/-- Sum of divisors: `σ(n) = Σ_{d ∣ n} d`. -/
def sigma (n : Nat) : Nat := divisorSum n (fun d => d)

/-- Number of divisors: `τ(n) = Σ_{d ∣ n} 1`. -/
def tau (n : Nat) : Nat := divisorSum n (fun _ => 1)

/-! ## Tables (∅-axiom, by `decide`) -/

/-- σ(1..12) = 1,3,4,7,6,12,8,15,13,18,12,28. -/
theorem sigma_table :
    sigma 1 = 1 ∧ sigma 2 = 3 ∧ sigma 3 = 4 ∧ sigma 4 = 7 ∧
    sigma 5 = 6 ∧ sigma 6 = 12 ∧ sigma 7 = 8 ∧ sigma 8 = 15 ∧
    sigma 9 = 13 ∧ sigma 10 = 18 ∧ sigma 11 = 12 ∧ sigma 12 = 28 := by
  decide

/-- τ(1..12) = 1,2,2,3,2,4,2,4,3,4,2,6. -/
theorem tau_table :
    tau 1 = 1 ∧ tau 2 = 2 ∧ tau 3 = 2 ∧ tau 4 = 3 ∧
    tau 5 = 2 ∧ tau 6 = 4 ∧ tau 7 = 2 ∧ tau 8 = 4 ∧
    tau 9 = 3 ∧ tau 10 = 4 ∧ tau 11 = 2 ∧ tau 12 = 6 := by
  decide

/-- σ(p) = p + 1 for the small primes 2,3,5,7,11,13. -/
theorem sigma_prime :
    sigma 2 = 3 ∧ sigma 3 = 4 ∧ sigma 5 = 6 ∧
    sigma 7 = 8 ∧ sigma 11 = 12 ∧ sigma 13 = 14 := by
  decide

/-- ★ **Perfect numbers**: `σ(n) = 2n` for n = 6, 28; non-perfect counterexamples.
    (Capped at 6, 28: `σ(496)` exceeds `decide`'s `maxRecDepth` on the `sumTo 496`
    unfolding.) -/
theorem perfect_table :
    sigma 6 = 12 ∧ sigma 28 = 56 ∧
    sigma 12 ≠ 24 ∧ sigma 8 ≠ 16 ∧ sigma 100 ≠ 200 := by
  decide

/-- σ(p^k) = 1 + p + … + p^k for small prime powers. -/
theorem sigma_prime_power :
    sigma 4 = 7 ∧ sigma 8 = 15 ∧ sigma 9 = 13 ∧ sigma 27 = 40 := by
  decide

end E213.Lib.Math.NumberTheory.SumOfDivisors
