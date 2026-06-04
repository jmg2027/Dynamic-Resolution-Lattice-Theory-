import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Meta.Int213.PolyIntMTactic

/-!
# EisensteinDivStep — ZOmega foundations for the `ℤ[ω]` division step

The norm-Euclidean property of `ℤ[ω]` (for `β ≠ 0`, a quotient `γ` with the remainder
`ρ = α − βγ` strictly smaller in norm) rounds each coordinate of `α·conj β` to the nearest
multiple of `N = ‖β‖²` (`CenteredDivision.centered_div`); the slick identity
`ρ · conj β = ⟨rre, rim⟩` (the centered remainders) plus the multiplicative norm and the
covering bound give `‖ρ‖²·N = rre² − rre·rim + rim² ≤ (3/4)N² < N²`, hence `‖ρ‖² < N`.

This file establishes the ZOmega-side foundations the assembly consumes:

  * `normSq_pos` — `β ≠ 0 → 0 < ‖β‖²`.
  * `mul_conj_self` — `β · conj β = ofInt ‖β‖²` (the norm realised as a ring element).
  * `normSq_conj` — `‖conj u‖² = ‖u‖²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Meta.Int213.Order (lt_of_sub_one_nonneg sub_zero ofNat_succ_sub_one)

/-! ## §1 — ZOmega helpers -/

/-- `‖conj u‖² = ‖u‖²`. -/
theorem normSq_conj (u : ZOmega) : u.conj.normSq = u.normSq := by
  cases u with
  | mk p q =>
    show (p - q) * (p - q) - (p - q) * (-q) + (-q) * (-q) = p * p - p * q + q * q
    ring_intZ

/-- `β · conj β = ofInt ‖β‖²` (the `re` is the norm, the `im` cancels). -/
theorem mul_conj_self (u : ZOmega) : u * u.conj = ZOmega.ofInt u.normSq := by
  cases u with
  | mk p q =>
    refine ZOmega.ext ?_ ?_
    · show p * (p - q) - q * (-q) = p * p - p * q + q * q
      ring_intZ
    · show p * (-q) + q * (p - q) - q * (-q) = 0
      have hz : p * (-q) + q * (p - q) - q * (-q) = q * q - q * q := by ring_intZ
      rw [hz, E213.Meta.Int213.Order.sub_self_zero]

/-- `β ≠ 0 → 0 < ‖β‖²`. -/
theorem normSq_pos (β : ZOmega) (hβ : β ≠ 0) : 0 < β.normSq := by
  have hne : β.normSq ≠ 0 := fun h => hβ ((normSq_eq_zero_iff β).mp h)
  have hnn : 0 ≤ β.normSq := normSq_nonneg β
  cases h : β.normSq with
  | ofNat n =>
    cases n with
    | zero => exact absurd h hne
    | succ m =>
      have hnn2 : (Int.ofNat (m + 1) - 0 - 1).NonNeg := by
        rw [sub_zero, ofNat_succ_sub_one]; exact ⟨m⟩
      exact lt_of_sub_one_nonneg hnn2
  | negSucc n =>
    rw [h] at hnn
    exact absurd hnn (by intro hc; cases hc)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
