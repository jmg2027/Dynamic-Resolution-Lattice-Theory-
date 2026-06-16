import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.PolyNatMTactic
import E213.Lib.Math.NumberTheory.DivisorMultiplicative
import E213.Lib.Math.NumberTheory.DivisorProductReindex
import E213.Lib.Math.NumberTheory.MobiusDivisorSum

/-!
# General summatory-multiplicative theorem (∅-axiom, Nat)

★★★ `summatory_mul` : if `f` is multiplicative on coprime pairs, then the
divisor-sum `g(n) = Σ_{d∣n} f(d)` is multiplicative.

This subsumes the per-function `sigma_mul` (f = id) and `tau_mul` (f ≡ 1) of
`DivisorMultiplicative`.  The Nat analogue of `MobiusDivisorSum.muStruct_divisorSum_mul`
(which proves the `Int`/`muStruct` instance); here `f` is a *hypothesis-multiplicative*
argument.

Engine (all reused):
  * `DivisorMultiplicative.divisor_product_reindex` — the sparse-fiber grid reindex
    (works for ANY `f`).
  * `DivisorProductReindex.divisorSum_mul_as_grid` — the EASY direction, product of
    divisor-sums as a grid double sum.
  * `MobiusDivisorSum.coprime_of_divisors` — divisors of coprimes are coprime, giving
    `gcd(i+1,k+1)=1` on surviving cells.
  * `DivisorMultiplicative.dvdInd_zero_or_one` / `dvdInd_eq_one_iff` — cell case split.

The ONLY new ingredient over `sigma_mul` is the per-cell rewrite
`f((i+1)(k+1)) = f(i+1)·f(k+1)` (via `hf` + cell coprimality), guarded by a
`dvdInd`-value case split so it is applied only on surviving cells.
-/

namespace E213.Lib.Math.NumberTheory.SummatoryMultiplicative

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.EulerTotient (divisorSum dvdInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (divisor_product_reindex dvdInd_zero_or_one dvdInd_eq_one_iff)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (divisorSum_mul_as_grid)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (coprime_of_divisors)

/-- **Cell factorization** for a multiplicative `f`: on each grid cell the integrand
    factors, `dvdInd i a · dvdInd k b · f((i+1)(k+1))
      = (dvdInd i a · f(i+1)) · (dvdInd k b · f(k+1))`.
    Guarded by the `dvdInd` value so `hf` is used only on surviving cells. -/
theorem cell_factor (f : Nat → Nat)
    (hf : ∀ x y, gcd213 x y = 1 → f (x * y) = f x * f y)
    {a b : Nat} (hab : gcd213 a b = 1) (i k : Nat) :
    dvdInd i a * dvdInd k b * f ((i + 1) * (k + 1))
      = (dvdInd i a * f (i + 1)) * (dvdInd k b * f (k + 1)) := by
  cases dvdInd_zero_or_one i a with
  | inl hi0 =>
    rw [hi0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  | inr hi1 =>
    cases dvdInd_zero_or_one k b with
    | inl hk0 =>
      rw [hk0, Nat.mul_zero, Nat.zero_mul, Nat.zero_mul, Nat.mul_zero]
    | inr hk1 =>
      have hia : (i + 1) ∣ a := (dvdInd_eq_one_iff i a).mp hi1
      have hkb : (k + 1) ∣ b := (dvdInd_eq_one_iff k b).mp hk1
      have hcop : gcd213 (i + 1) (k + 1) = 1 := coprime_of_divisors hab hia hkb
      have hmm : f ((i + 1) * (k + 1)) = f (i + 1) * f (k + 1) := hf _ _ hcop
      rw [hmm]
      generalize dvdInd i a = DA
      generalize dvdInd k b = DB
      generalize f (i + 1) = F1
      generalize f (k + 1) = F2
      ring_nat

/-- ★★★ **General summatory-multiplicative theorem**: `f` multiplicative on coprime
    pairs ⟹ `g(n) = Σ_{d∣n} f(d)` is multiplicative.
    `gcd(a,b)=1 → 0<a → 0<b → divisorSum (a·b) f = divisorSum a f · divisorSum b f`. -/
theorem summatory_mul (f : Nat → Nat)
    (hf : ∀ a b, gcd213 a b = 1 → f (a * b) = f a * f b)
    {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) :
    divisorSum (a * b) f = divisorSum a f * divisorSum b f := by
  rw [divisor_product_reindex a b hab ha hb f]
  rw [divisorSum_mul_as_grid a b f]
  exact sumTo_congr a _ _ (fun i _ =>
    sumTo_congr b _ _ (fun k _ => cell_factor f hf hab i k))

/-! ## Corollaries — the per-function instances as one-liners -/

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma tau)

/-- `id` is multiplicative: `(x·y) = x·y`. -/
theorem id_mul (x y : Nat) (_ : gcd213 x y = 1) : (x * y) = x * y := rfl

/-- ★★ `sigma` multiplicative — corollary of `summatory_mul` at `f = id`. -/
theorem sigma_mul {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) :
    sigma (a * b) = sigma a * sigma b :=
  summatory_mul (fun d => d) (fun x y h => id_mul x y h) hab ha hb

/-- `fun _ => 1` is multiplicative: `1 = 1·1`. -/
theorem const_one_mul (x y : Nat) (_ : gcd213 x y = 1) : (1 : Nat) = 1 * 1 := rfl

/-- ★★ `tau` multiplicative — corollary of `summatory_mul` at `f ≡ 1`. -/
theorem tau_mul {a b : Nat} (hab : gcd213 a b = 1) (ha : 0 < a) (hb : 0 < b) :
    tau (a * b) = tau a * tau b :=
  summatory_mul (fun _ => 1) (fun x y h => const_one_mul x y h) hab ha hb

end E213.Lib.Math.NumberTheory.SummatoryMultiplicative
