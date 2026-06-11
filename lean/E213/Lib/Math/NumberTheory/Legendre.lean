import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# Legendre — `vₚ(n!)` as a sum, ∅-axiom

Legendre's factorial formula `vₚ(n!) = Σⱼ₌₁ ⌊n/pʲ⌋` splits into two halves:

  1. **Additivity over the factorial product** (this file):
     `vₚ(n!) = Σ_{k<n} vₚ(k+1)` — immediate from `PrimeValuation.vp_mul`
     (`vₚ(a·b) = vₚa + vₚb`) by induction on `n!  = (n)·(n-1)!`, with `vₚ 1 = 0`.
  2. **Double counting** (the remaining half, recorded on the frontier):
     `Σ_{k<n} vₚ(k+1) = Σⱼ ⌊n/pʲ⌋`, by swapping the order of summation
     (`vₚ(k+1) = #{j ≥ 1 : pʲ ∣ k+1}` and `Σ_{k<n} [pʲ ∣ k+1] = ⌊n/pʲ⌋`).

Half 1 already turns the factorial-valuation into a *finite explicit sum*, which is
the form the ζ(3) lcm-bound brick's key-divisibility step consumes per prime power
(against the counting lemma `LcmGrowthChebyshev.count30`).

  * `vp_one` — `vₚ 1 = 0` (`p ≥ 2`).
  * ★★★ `vp_factorial` — `vₚ(n!) = Σ_{k<n} vₚ(k+1)`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Legendre

open E213.Meta.Nat.Valuation (vp vp_lt)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_zero
  factorial_succ factorial_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- `vₚ 1 = 0` for `p ≥ 2`: the valuation is strictly below its argument. -/
theorem vp_one {p : Nat} (hp : 2 ≤ p) : vp p 1 = 0 :=
  Nat.le_zero.mp (Nat.le_of_lt_succ (vp_lt p 1 hp (by decide)))

/-- ★★★ **`vₚ(n!)` as a finite sum**: `vₚ(n!) = Σ_{k<n} vₚ(k+1)`, by induction on the
    factorial product `(n+1)! = (n+1)·n!` through `PrimeValuation.vp_mul`. -/
theorem vp_factorial {p : Nat} (hp : Prime213 p) :
    ∀ n, vp p (factorial n) = sumTo n (fun k => vp p (k + 1))
  | 0 => by
    show vp p (factorial 0) = 0
    rw [factorial_zero]; exact vp_one hp.1
  | n + 1 => by
    rw [factorial_succ, vp_mul hp (Nat.succ_pos n) (factorial_pos n),
        vp_factorial hp n, sumTo_succ]
    exact Nat.add_comm _ _

end E213.Lib.Math.NumberTheory.Legendre
