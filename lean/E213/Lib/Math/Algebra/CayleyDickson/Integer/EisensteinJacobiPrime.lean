import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime

/-!
# The Jacobi sum is a prime of `ℤ[ω]` (∅-axiom, Phase A4)

`N(J)=p` (`jacobi_norm`) makes the cubic Jacobi sum an element of norm a rational prime `p ≡ 1 mod 3`,
hence a **prime element** of `ℤ[ω]`:

  `J ∣ α·β  ⟹  J ∣ α ∨ J ∣ β`   (`jacobi_prime`),

a direct instance of `EisensteinPrime.norm_prime_euclid` with `π = jacobiSum p m x`.  So `J = π` up to
a unit (the prime above `p`); fixing the unit is the *primary* normalisation (`J ≡ −1 mod 3`), the
remaining A4 step before the cubic reciprocity law `(π/π')₃=(π'/π)₃`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiPrime

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw (jacobi_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime (norm_prime_euclid)

/-- ★★★★★ **The cubic Jacobi sum is prime in `ℤ[ω]`** — for a prime `p ≡ 1 mod 3` (`p>3`),
    `jacobiSum p m x ∣ α·β ⟹ jacobiSum p m x ∣ α ∨ jacobiSum p m x ∣ β`.  Immediate from `N(J)=p`
    (`jacobi_norm`) via `norm_prime_euclid`.  ∅-axiom. -/
theorem jacobi_prime {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) {α β : ZOmega} (hdvd : jacobiSum p m x ∣ α * β) :
    jacobiSum p m x ∣ α ∨ jacobiSum p m x ∣ β :=
  norm_prime_euclid hpr hp (jacobi_norm hp hp3 hpr h3m hm1 hdn hω hx) hdvd

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiPrime
