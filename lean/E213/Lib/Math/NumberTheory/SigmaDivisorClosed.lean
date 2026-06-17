import E213.Lib.Math.NumberTheory.SigmaPrimePowGeom
import E213.Lib.Math.NumberTheory.MobiusDivisorSum

/-!
# σ_m on a prime power: the actual divisor sum equals the geometric closed form (∅-axiom)

`SigmaPrimePowGeom.sigma_prime_pow_geom` gives the geometric identity for the *abstract* sum
`Σ_{i=0}^{k} p^{m·i}`.  This file connects it to the genuine **divisor sum**
`divisorSumZ (pᵏ) (fun d ↦ dᵐ)` — the value of the divisor-power function `σ_m` at a prime
power — via the prime-power reindex (`divisorSumZ_prime_pow_reindex`) and the cast-power bridge
(`ofNat_pow_eq_ipow`).  Result (cleared form):

> `(pᵐ − 1) · σ_m(pᵏ) = p^{m·(k+1)} − 1`  with  `σ_m(pᵏ) = Σ_{d ∣ pᵏ} dᵐ`.

Two `sumZ` definitions coexist in the corpus (the geometric-series one and the Möbius-divisor
one — textually identical recursions); `sumZ_bridge` identifies them so the two toolboxes compose.
-/

namespace E213.Lib.Math.NumberTheory.SigmaDivisorClosed

open E213.Lib.Math.NumberTheory.DiffPowDvd (ipow ipow_mul ofNat_pow_eq_ipow)
open E213.Lib.Math.NumberTheory.SigmaPrimePowGeom (sigma_prime_pow_geom)
open E213.Lib.Math.NumberTheory.MobiusFunction (divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (divisorSumZ_prime_pow_reindex sumZ_eq_sumPowZ)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)

/-- The two corpus `sumZ` recursions (geometric-series and Möbius-divisor) agree pointwise. -/
theorem sumZ_bridge (f : Nat → Int) :
    ∀ n, E213.Lib.Math.NumberTheory.MobiusFunction.sumZ n f
        = E213.Lib.Math.NumberTheory.GeometricSeries.sumZ n f
  | 0     => rfl
  | n + 1 => by
      show E213.Lib.Math.NumberTheory.MobiusFunction.sumZ n f + f n
         = E213.Lib.Math.NumberTheory.GeometricSeries.sumZ n f + f n
      rw [sumZ_bridge f n]

/-- ★★★ **σ_m at a prime power, cleared geometric form** (∅-axiom):
    `(pᵐ − 1) · (Σ_{d ∣ pᵏ} dᵐ) = p^{m·(k+1)} − 1`.

    The genuine divisor-power sum `σ_m(pᵏ) = Σ_{d ∣ pᵏ} dᵐ` collapses (via the prime-power
    reindex `Σ_{d ∣ pᵏ} = Σ_{i=0}^{k}` on `d = pⁱ`) onto the geometric series of ratio `pᵐ`,
    whose cleared closed form is the right-hand side. -/
theorem sigma_prime_pow_divisor_geom {p : Nat} (hp : Prime213 p) (m k : Nat) :
    (ipow (Int.ofNat p) m - 1)
        * divisorSumZ (p ^ k) (fun d => ipow (Int.ofNat d) m)
      = ipow (Int.ofNat p) (m * (k + 1)) - 1 := by
  -- reindex the divisor sum onto `Σ_{i=0}^{k} (pⁱ)ᵐ`
  rw [divisorSumZ_prime_pow_reindex hp k (fun d => ipow (Int.ofNat d) m),
      ← sumZ_eq_sumPowZ (fun d => ipow (Int.ofNat d) m) p k,
      sumZ_bridge (fun i => ipow (Int.ofNat (p ^ i)) m) (k + 1)]
  -- rewrite each term `(pⁱ)ᵐ = p^{m·i}` and apply the geometric closed form
  rw [E213.Lib.Math.NumberTheory.SigmaPrimePowGeom.sumZ_congr (k + 1)
        (fun i => ipow (Int.ofNat (p ^ i)) m)
        (fun i => ipow (Int.ofNat p) (m * i))
        (fun i => by
          show ipow (Int.ofNat (p ^ i)) m = ipow (Int.ofNat p) (m * i)
          rw [ofNat_pow_eq_ipow p i, ← ipow_mul (Int.ofNat p) i m, Nat.mul_comm i m]),
      sigma_prime_pow_geom (Int.ofNat p) m k]

end E213.Lib.Math.NumberTheory.SigmaDivisorClosed
