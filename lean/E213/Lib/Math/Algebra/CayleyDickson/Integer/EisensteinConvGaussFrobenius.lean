import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBasis
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFreshman

/-!
# The Gauss-sum Frobenius — first half — `g(χ)^{⋆q} ≡ Σ_t χ(t)^q · e_{tq%p} (mod q)`

★★★★★ `gauss_pow_modEq` : the group-ring Frobenius applied to the Gauss sum, coefficient-wise:

  `g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ(t)^q · e_{(t·q)%p}(k)   (mod ofInt q)`   for prime `q`, `k < p`.

This assembles three closed pieces, no new machinery:
1. `gauss_eq_sum_basis` (under `convPow_congr`) rewrites `g(χ) = Σ_t χ(t)·e_t` inside the `⋆`-power;
2. the convolution multinomial Frobenius `convPow_sum_modEq_prime` pushes the `q`-th `⋆`-power through
   the finite sum: `(Σ_t χ(t)·e_t)^{⋆q} ≡ Σ_t (χ(t)·e_t)^{⋆q} (mod q)`;
3. `scaledBasisPow_eq` evaluates each term `(χ(t)·e_t)^{⋆q}(k) = χ(t)^q · e_{tq%p}(k)`.

This is the **first half** of the Frobenius congruence `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)`.  The remaining
**second half** is the number-theory fold: `χ(t)^q = χ̄(t)` (μ₃ + `q ≡ 2 mod 3`) and the `t ↦ tq%p`
reindex (a permutation of `[0,p)`) that collapses `Σ_t χ̄(t)·e_{tq%p}` into `χ̄(q)·g(χ)`.

∅-axiom up to allowed `propext` (inherited from `convPow_sum_modEq_prime` / `scaledBasisPow_eq`).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussFrobenius

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow (convPow convPow_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFreshman (convPow_sum_modEq_prime)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBasis
  (basis scaledBasisPow_eq gauss_eq_sum_basis)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)

/-- ★★★★★ **The Gauss-sum Frobenius, first half** —
    `g(χ)^{⋆q}(k) ≡ Σ_{t<p} χ(t)^q · e_{(t·q)%p}(k)   (mod ofInt q)`   for a prime `q` and `k < p`.

    `convPow_congr` swaps `g(χ)` for `Σ_t χ(t)·e_t` inside the `⋆`-power (`gauss_eq_sum_basis`); the
    convolution multinomial Frobenius `convPow_sum_modEq_prime` distributes the `q`-th `⋆`-power across
    the finite sum; and `scaledBasisPow_eq` evaluates each per-`t` term as `χ(t)^q · e_{tq%p}`.  The
    first half of `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)`.  ∅-axiom up to allowed `propext`. -/
theorem gauss_pow_modEq (p m x q : Nat) (hp : 0 < p) (hq : 1 < q)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) {k : Nat} (hk : k < p) :
    ModEq (ofInt ((q : Nat) : Int))
      (convPow p (gauss p m x) q k)
      (sumRange (fun t => pow (chiOmega p m x t) q * basis ((t * q) % p) k) p) := by
  -- 1. rewrite g(χ) = Σ_t χ(t)·e_t inside the ⋆-power
  have hcong : convPow p (gauss p m x) q k
      = convPow p (fun i => sumRange (fun t => chiOmega p m x t * basis t i) p) q k :=
    convPow_congr p hp (fun i hi => gauss_eq_sum_basis hi) q hk
  -- 3. each per-t term evaluates to χ(t)^q · e_{tq%p}
  have hrhs : sumRange (fun t => convPow p (fun i => chiOmega p m x t * basis t i) q k) p
      = sumRange (fun t => pow (chiOmega p m x t) q * basis ((t * q) % p) k) p :=
    sum_congr p (fun t ht => scaledBasisPow_eq hp ht (chiOmega p m x t) q hk)
  -- 2. the convolution multinomial Frobenius distributes the ⋆-power across the sum
  rw [hcong, ← hrhs]
  exact convPow_sum_modEq_prime p (fun t i => chiOmega p m x t * basis t i) q hq hqr hk p

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussFrobenius
