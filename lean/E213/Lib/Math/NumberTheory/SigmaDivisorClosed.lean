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

open E213.Lib.Math.NumberTheory.DiffPowDvd (ipow ipow_mul ipow_base_mul ofNat_pow_eq_ipow)
open E213.Lib.Math.NumberTheory.SigmaPrimePowGeom (sigma_prime_pow_geom)
open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (divisorSumZ_prime_pow_reindex sumZ_eq_sumPowZ divisorSumZ_product_reindex
   inner_factor sumZ_mul_right)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase (sumZ_congr)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Tactic.NatHelper (gcd213)

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

/-- The σ_m summand `d ↦ dᵐ` is **completely multiplicative**:
    `(u·v)ᵐ = uᵐ · vᵐ` for all `u, v` (no coprimality needed). -/
theorem ipow_ofNat_mul (m u v : Nat) :
    ipow (Int.ofNat (u * v)) m = ipow (Int.ofNat u) m * ipow (Int.ofNat v) m := by
  rw [show Int.ofNat (u * v) = Int.ofNat u * Int.ofNat v from Int.ofNat_mul u v, ipow_base_mul]

/-- Each cell of the product reindex factors (complete multiplicativity of `dᵐ`):
    `dᵢ · dₖ · ((i+1)(k+1))ᵐ = (dᵢ·(i+1)ᵐ) · (dₖ·(k+1)ᵐ)`. -/
theorem sigma_m_cell_factor (m : Nat) {a b : Nat} (i k : Nat) :
    (dvdInd i a : Int) * (dvdInd k b : Int) * ipow (Int.ofNat ((i + 1) * (k + 1))) m
      = ((dvdInd i a : Int) * ipow (Int.ofNat (i + 1)) m)
          * ((dvdInd k b : Int) * ipow (Int.ofNat (k + 1)) m) := by
  rw [ipow_ofNat_mul m (i + 1) (k + 1),
      E213.Meta.Int213.mul_mul_mul_comm (dvdInd i a : Int) (dvdInd k b : Int)
        (ipow (Int.ofNat (i + 1)) m) (ipow (Int.ofNat (k + 1)) m)]

/-- ★★★ **σ_m is multiplicative over coprime products** (∅-axiom):
    for coprime `a, b > 0`, `σ_m(a·b) = σ_m(a)·σ_m(b)` with `σ_m(n) = Σ_{d ∣ n} dᵐ`.

    Mirrors `muStruct_divisorSum_mul`: reindex the product, factor each cell via
    complete multiplicativity of `dᵐ`, then separate the double sum.  Combined with
    `sigma_prime_pow_divisor_geom`, this yields σ_m on every `n` from its factorization. -/
theorem sigma_m_mul {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) (m : Nat) :
    divisorSumZ (a * b) (fun d => ipow (Int.ofNat d) m)
      = divisorSumZ a (fun d => ipow (Int.ofNat d) m)
          * divisorSumZ b (fun d => ipow (Int.ofNat d) m) := by
  rw [divisorSumZ_product_reindex a b hab ha hb (fun d => ipow (Int.ofNat d) m)]
  -- factor each cell
  rw [sumZ_congr a _
        (fun i => sumZ b (fun k =>
          ((dvdInd i a : Int) * ipow (Int.ofNat (i + 1)) m)
            * ((dvdInd k b : Int) * ipow (Int.ofNat (k + 1)) m)))
        (fun i _ => sumZ_congr b _ _ (fun k _ => sigma_m_cell_factor m i k))]
  -- pull the i-part out of each inner b-sum
  rw [sumZ_congr a _
        (fun i => ((dvdInd i a : Int) * ipow (Int.ofNat (i + 1)) m)
            * sumZ b (fun k => (dvdInd k b : Int) * ipow (Int.ofNat (k + 1)) m))
        (fun i _ => inner_factor ((dvdInd i a : Int) * ipow (Int.ofNat (i + 1)) m) b
          (fun k => (dvdInd k b : Int) * ipow (Int.ofNat (k + 1)) m))]
  -- pull the constant b-sum out of the a-sum
  rw [sumZ_mul_right (sumZ b (fun k => (dvdInd k b : Int) * ipow (Int.ofNat (k + 1)) m)) a
        (fun i => (dvdInd i a : Int) * ipow (Int.ofNat (i + 1)) m)]
  rfl

end E213.Lib.Math.NumberTheory.SigmaDivisorClosed
