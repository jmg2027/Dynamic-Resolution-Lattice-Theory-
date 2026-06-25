import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega

/-!
# Multiplicative cubic-character orthogonality — `Σ_{j<3k} ωʲ = 0` (∅-axiom)

★★★★★ `geomSum_omega_three_mul` : the partial geometric sum of `ω` over any **multiple-of-three**
range vanishes,

  `Σ_{j=0}^{3k−1} ωʲ = 0`.

This is the **multiplicative character orthogonality** of the cubic character realised on `ℤ[ω]`: the
cubic character `χ(gⁱ) = ωⁱ` summed over a full cycle (`p − 1 = 3m` values, `p ≡ 1 mod 3`) is `0` — the
key cancellation behind the norm `N(J) = p` of the **Jacobi sum** `J(χ,χ)`.  Each consecutive block of
three terms `ω^{3j} + ω^{3j+1} + ω^{3j+2} = ω^{3j}·(1 + ω + ω²) = 0` (`ω³=1`,
`RootOfUnityOrthogonality.omega_orthogonality`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharOrthogonality

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (pow one pow_succ geomSum geomSum_succ one_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega (pow_omega_three_mul)
open E213.Meta.Algebra213.Ring213 (add_assoc add_zero)

/-- **One period of `ω` cancels** — when `ωⁿ = 1`, advancing the partial sum by three terms leaves it
    unchanged: `Σ_{j<n+3} ωʲ = Σ_{j<n} ωʲ` (the added block `ωⁿ + ω^{n+1} + ω^{n+2} = 1 + ω + ω² = 0`). -/
theorem geomSum_omega_step (n : Nat) (hn : pow Omega n = one) :
    geomSum Omega (n + 3) = geomSum Omega n := by
  have p1 : pow Omega (n + 1) = Omega := by rw [pow_succ, hn, one_mul]
  have p2 : pow Omega (n + 2) = Omega * Omega := by
    rw [show n + 2 = n + 1 + 1 from rfl, pow_succ, p1]
  have hblock : one + (Omega + Omega * Omega) = (0 : ZOmega) := by decide
  show geomSum Omega (n + 2 + 1) = geomSum Omega n
  rw [geomSum_succ, geomSum_succ, geomSum_succ, hn, p1, p2, add_assoc, add_assoc, hblock, add_zero]

/-- ★★★★★ **Multiplicative cubic-character orthogonality.**  `Σ_{j=0}^{3k−1} ωʲ = 0` — the cubic
    character summed over a full cycle vanishes.  Induction on `k` with `geomSum_omega_step` (each new
    block of three is killed by `1 + ω + ω² = 0`, using `ω^{3k} = 1`).  ∅-axiom. -/
theorem geomSum_omega_three_mul : ∀ k : Nat, geomSum Omega (3 * k) = 0
  | 0 => rfl
  | k + 1 => by
      rw [Nat.mul_succ, geomSum_omega_step (3 * k) (pow_omega_three_mul k)]
      exact geomSum_omega_three_mul k

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharOrthogonality
