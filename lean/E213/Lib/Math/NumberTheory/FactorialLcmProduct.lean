import E213.Lib.Math.NumberTheory.FactorialLcmIdentity
import E213.Lib.Math.NumberTheory.FTAEquality

/-!
# The two homes of `e`: `N! = Π_{i=1}^{N} lcm(1..⌊N/i⌋)` (∅-axiom)

`e` lives in two places: the factorial (`e = Σ 1/k!`) and the lcm growth
(`lcm(1..N) ~ eᴺ`, the PNT/`ψ` side).  The corpus already proves their *per-prime* bridge,
`FactorialLcmIdentity.vp_factorial_eq_sum_vp_lcm`:
`vp p (N!) = Σ_{i<N} vp p (lcm(1..⌊N/(i+1)⌋))`.  This file lifts that exponent identity to the
**product identity** itself — the factorial *is* the product of the lcm's — by matching prime
valuations (`FTAEquality.eq_of_vp_eq`).  One cross-domain object (`N!`) read as a product over
the lcm-growth side, the two homes of `e` welded by the prime-exponent vector.
-/

namespace E213.Lib.Math.NumberTheory.FactorialLcmProduct

open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_self_pow)
open E213.Meta.Nat.Valuation (vp)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (lcmUpTo lcmUpTo_pos)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_pos)
open E213.Lib.Math.NumberTheory.FTAEquality (eq_of_vp_eq)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (vp_factorial_eq_sum_vp_lcm)

/-! ## §1 — range product and its valuation -/

/-- `Π_{i<n} F i`. -/
def prodTo : Nat → (Nat → Nat) → Nat
  | 0,     _ => 1
  | n + 1, F => prodTo n F * F n

theorem prodTo_pos (F : Nat → Nat) (hF : ∀ i, 0 < F i) : ∀ n, 0 < prodTo n F
  | 0     => Nat.one_pos
  | n + 1 => Nat.mul_pos (prodTo_pos F hF n) (hF n)

/-- ★★ **`vp` of a range product is the sum of the `vp`s** (factor positivity needed for
    `vp_mul`): `vp p (Π_{i<n} F i) = Σ_{i<n} vp p (F i)`. -/
theorem vp_prod {p : Nat} (hp : IsPrime213 p) (F : Nat → Nat) (hF : ∀ i, 0 < F i) :
    ∀ n, vp p (prodTo n F) = sumTo n (fun i => vp p (F i))
  | 0     => by
      show vp p 1 = 0
      have h0 := vp_self_pow hp 0
      rwa [Nat.pow_zero] at h0
  | n + 1 => by
      show vp p (prodTo n F * F n) = sumTo n (fun i => vp p (F i)) + vp p (F n)
      rw [vp_mul hp (prodTo_pos F hF n) (hF n), vp_prod hp F hF n]

/-! ## §2 — the product identity -/

/-- ★★★ **The factorial is the product of the lcm's** — `N! = Π_{i=1}^{N} lcm(1..⌊N/i⌋)`
    (indices `i+1`, `i < N`).  The two homes of `e` welded: proved by matching prime exponents,
    `vp p (N!) = Σ_{i<N} vp p (lcm(1..⌊N/(i+1)⌋)) = vp p (Π …)`, then `eq_of_vp_eq`. ∅-axiom. -/
theorem factorial_eq_prod_lcm (N : Nat) :
    factorial N = prodTo N (fun i => lcmUpTo (N / (i + 1))) := by
  refine eq_of_vp_eq (factorial_pos N)
    (prodTo_pos (fun i => lcmUpTo (N / (i + 1))) (fun i => lcmUpTo_pos _) N) ?_
  intro p hp
  rw [vp_factorial_eq_sum_vp_lcm hp N,
      vp_prod hp (fun i => lcmUpTo (N / (i + 1))) (fun i => lcmUpTo_pos _) N]

/-- Smoke: `5! = 120 = lcm(1..5)·lcm(1..2)·lcm(1..1)·lcm(1..1)·lcm(1..1) = 60·2·1·1·1`. -/
theorem factorial_eq_prod_lcm_smoke :
    factorial 5 = prodTo 5 (fun i => lcmUpTo (5 / (i + 1))) :=
  factorial_eq_prod_lcm 5

end E213.Lib.Math.NumberTheory.FactorialLcmProduct
