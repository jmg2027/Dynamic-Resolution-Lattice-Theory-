import E213.Lib.Math.NumberTheory.DivisorMultiplicative
import E213.Meta.Nat.Iterate213

/-!
# Generalized divisor function `σ_k(n) = Σ_{d∣n} d^k` and its multiplicativity (∅-axiom)

  * `sigmaK k n = divisorSum n (fun d => d^k)`  (`σ_0 = τ`, `σ_1 = σ`).
  * ★★★ `sigmaK_mul` : σ_k is multiplicative over coprime products, for **all k**.

Mirrors `DivisorMultiplicative.sigma_mul` (the `k=1` case) with `f = (·^k)`; the only
new ingredient is the per-cell power-factorization `((i+1)(j+1))^k = (i+1)^k·(j+1)^k`
(`Iterate213.mul_pow_pure`, PURE; core `Nat.mul_pow` carries `propext`), so the
reindexed grid factors and `sigmaK_mul` discharges via `divisor_product_reindex`.
Genuinely absent (the corpus had only `sigma`=σ_1 and `tau`=σ_0).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.GeneralizedDivisorSum

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTotient (divisorSum dvdInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (divisorSum_mul_as_grid)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative (divisor_product_reindex)
open E213.Meta.Nat.Iterate213 (mul_pow_pure)

/-- `σ_k(n) = Σ_{d ∣ n} d^k`. -/
def sigmaK (k n : Nat) : Nat := divisorSum n (fun d => d ^ k)

/-- `σ_0 = τ`. -/
theorem sigmaK_zero (n : Nat) : sigmaK 0 n = divisorSum n (fun _ => 1) := by
  show divisorSum n (fun d => d ^ 0) = divisorSum n (fun _ => 1)
  rfl

/-- `σ_1 = σ`. -/
theorem sigmaK_one (n : Nat) : sigmaK 1 n = divisorSum n (fun d => d) := by
  show divisorSum n (fun d => d ^ 1) = divisorSum n (fun d => d)
  refine sumTo_congr n _ _ (fun j _ => ?_)
  show dvdInd j n * (j + 1) ^ 1 = dvdInd j n * (j + 1)
  rw [Nat.pow_one]

/-- ★ **Conditional `σ_k`-multiplicativity**: given the divisor-product reindex for
    `f = (·^k)` on `a·b`, `σ_k (a·b) = σ_k a · σ_k b`. -/
theorem sigmaK_mul_of_reindex (k : Nat) {a b : Nat}
    (Hreindex : divisorSum (a * b) (fun d => d ^ k)
      = sumTo a (fun i => sumTo b (fun j =>
          dvdInd i a * dvdInd j b * ((i + 1) * (j + 1)) ^ k))) :
    sigmaK k (a * b) = sigmaK k a * sigmaK k b := by
  show divisorSum (a * b) (fun d => d ^ k)
      = divisorSum a (fun d => d ^ k) * divisorSum b (fun d => d ^ k)
  rw [divisorSum_mul_as_grid a b (fun d => d ^ k), Hreindex]
  refine sumTo_congr a _ _ (fun i _ => sumTo_congr b _ _ (fun j _ => ?_))
  rw [mul_pow_pure (i + 1) (j + 1) k]
  generalize dvdInd i a = DA
  generalize dvdInd j b = DB
  generalize (i + 1) ^ k = P
  generalize (j + 1) ^ k = Q
  ring_nat

/-- ★★★ **σ_k is multiplicative over coprime products** (all k):
    `gcd(a,b)=1 → 0<a → 0<b → σ_k (a·b) = σ_k a · σ_k b`. -/
theorem sigmaK_mul (k : Nat) {a b : Nat} (hab : gcd213 a b = 1)
    (ha : 0 < a) (hb : 0 < b) :
    sigmaK k (a * b) = sigmaK k a * sigmaK k b :=
  sigmaK_mul_of_reindex k (divisor_product_reindex a b hab ha hb (fun d => d ^ k))

/-- Smoke: σ_2(12)=σ_2(4)·σ_2(3)=210, σ_2(15)=σ_2(3)·σ_2(5), σ_3(12)=σ_3(4)·σ_3(3). -/
theorem sigmaK_mul_smoke :
    sigmaK 2 12 = sigmaK 2 4 * sigmaK 2 3
    ∧ sigmaK 2 15 = sigmaK 2 3 * sigmaK 2 5
    ∧ sigmaK 3 12 = sigmaK 3 4 * sigmaK 3 3 :=
  ⟨sigmaK_mul 2 (a := 4) (b := 3) (by decide) (by decide) (by decide),
   sigmaK_mul 2 (a := 3) (b := 5) (by decide) (by decide) (by decide),
   sigmaK_mul 3 (a := 4) (b := 3) (by decide) (by decide) (by decide)⟩

/-- Smoke: concrete values. -/
theorem sigmaK_values :
    sigmaK 2 4 = 21 ∧ sigmaK 2 3 = 10 ∧ sigmaK 2 12 = 210
    ∧ sigmaK 0 6 = 4 ∧ sigmaK 1 6 = 12 := by
  decide

end E213.Lib.Math.NumberTheory.GeneralizedDivisorSum
