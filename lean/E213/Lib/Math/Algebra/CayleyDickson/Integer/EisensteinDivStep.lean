import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinEuclidean
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.PolyIntMTactic

/-!
# EisensteinDivStep — ZOmega foundations for the `ℤ[ω]` division step

The norm-Euclidean property of `ℤ[ω]` (for `β ≠ 0`, a quotient `γ` with the remainder
`ρ = α − βγ` strictly smaller in norm) rounds each coordinate of `α·conj β` to the nearest
multiple of `N = ‖β‖²` (`CenteredDivision.centered_div`); the slick identity
`ρ · conj β = ⟨rre, rim⟩` (the centered remainders) plus the multiplicative norm and the
covering bound give `‖ρ‖²·N = rre² − rre·rim + rim² ≤ (3/4)N² < N²`, hence `‖ρ‖² < N`.

  * `normSq_pos` — `β ≠ 0 → 0 < ‖β‖²`.
  * `mul_conj_self` — `β · conj β = ofInt ‖β‖²` (the norm realised as a ring element).
  * `normSq_conj` — `‖conj u‖² = ‖u‖²`.
  * `rho_conj_eq` — `(α − βγ)·conjβ = ⟨(α·conjβ).re − qre·N, (α·conjβ).im − qim·N⟩`.
  * `div_step_ineq` — `8(P·N) ≤ 6N²`, `0 < N` ⟹ `P < N`.
  * ★★★★ `zomega_div_step` — `β ≠ 0 → ∃ γ ρ, α = βγ + ρ ∧ ‖ρ‖² < ‖β‖²`: **`ℤ[ω]` is
    norm-Euclidean**, the foundational pillar of the split-prime descent.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int_sq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinEuclidean (covering_bound)
open E213.Meta.Int213 (mul_nonneg mul_assoc)
open E213.Meta.Int213.OrderMul
  (mul_le_mul_left_nonneg int_sign mul_pos int_lt_irrefl)
open E213.Meta.Int213.Order
  (lt_of_sub_one_nonneg sub_zero zero_sub ofNat_succ_sub_one le_of_sub_nonneg nonneg_of_le_zero
   le_of_lt lt_of_le_of_lt lt_of_sub_pos sub_pos_of_lt le_trans)

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

/-! ## §2 — the fixed-point-form remainder identity and the division step -/

/-- The remainder `ρ = α − βγ` times `conj β` has coordinates equal to the rounding
    remainders of `α·conj β` against `N = ‖β‖²`: `ρ · conj β = ⟨(α·conjβ).re − qre·N,
    (α·conjβ).im − qim·N⟩`. -/
theorem rho_conj_eq (α β : ZOmega) (qre qim : Int) :
    (α - β * ⟨qre, qim⟩) * β.conj
      = ⟨(α * β.conj).re - qre * β.normSq, (α * β.conj).im - qim * β.normSq⟩ := by
  cases α with
  | mk ax ay =>
  cases β with
  | mk bx bz =>
    refine ZOmega.ext ?_ ?_
    · show (ax + -(bx * qre - bz * qim)) * (bx - bz)
            - (ay + -(bx * qim + bz * qre - bz * qim)) * (-bz)
         = (ax * (bx - bz) - ay * (-bz)) - qre * (bx * bx - bx * bz + bz * bz)
      ring_intZ
    · show (ax + -(bx * qre - bz * qim)) * (-bz)
            + (ay + -(bx * qim + bz * qre - bz * qim)) * (bx - bz)
            - (ay + -(bx * qim + bz * qre - bz * qim)) * (-bz)
         = (ax * (-bz) + ay * (bx - bz) - ay * (-bz)) - qim * (bx * bx - bx * bz + bz * bz)
      ring_intZ

/-- The closing inequality: `8(P·N) ≤ 6N²` with `0 < N` forces `P < N`.  (If `N ≤ P` then
    `8N² ≤ 8(P·N) ≤ 6N²`, so `2N² ≤ 0`, contradicting `0 < N²`.) -/
theorem div_step_ineq {P N : Int} (hNpos : 0 < N)
    (hcov : 8 * (P * N) ≤ 6 * (N * N)) : P < N := by
  rcases int_sign (P - N) with hge | hlt
  · exfalso
    have hNle : N ≤ P := le_of_sub_nonneg (nonneg_of_le_zero hge)
    have h8N : (0 : Int) ≤ 8 * N := mul_nonneg (by decide) (le_of_lt hNpos)
    have hmul : 8 * (N * N) ≤ 8 * (P * N) := by
      have hx := mul_le_mul_left_nonneg hNle (8 * N) h8N
      rw [show (8 * N) * N = 8 * (N * N) from by ring_intZ,
          show (8 * N) * P = 8 * (P * N) from by ring_intZ] at hx
      exact hx
    have hstep : 8 * (N * N) ≤ 6 * (N * N) := le_trans hmul hcov
    have hNN : 0 < N * N := mul_pos hNpos hNpos
    have h2NN : 0 < 2 * (N * N) := mul_pos (by decide) hNN
    have h68 : 6 * (N * N) < 8 * (N * N) := by
      apply lt_of_sub_pos
      rw [show 8 * (N * N) - 6 * (N * N) = 2 * (N * N) from by ring_intZ]
      exact h2NN
    exact int_lt_irrefl (8 * (N * N)) (lt_of_le_of_lt hstep h68)
  · have h2 : 0 < (0 : Int) - (P - N) := sub_pos_of_lt hlt
    rw [zero_sub, show -(P - N) = N - P from by ring_intZ] at h2
    exact lt_of_sub_pos h2

/-- ★★★★ **The `ℤ[ω]` division step (norm-Euclidean).**  For `β ≠ 0` there is a quotient `γ`
    whose remainder `ρ = α − βγ` is strictly smaller in norm: `‖ρ‖² < ‖β‖²`.  `γ` rounds each
    coordinate of `α·conj β` to the nearest multiple of `N = ‖β‖²`; then
    `‖ρ‖²·N = rre² − rre·rim + rim² ≤ (3/4)N² < N²` (`covering_bound`), so `‖ρ‖² < N`. -/
theorem zomega_div_step (α β : ZOmega) (hβ : β ≠ 0) :
    ∃ γ ρ : ZOmega, α = β * γ + ρ ∧ ρ.normSq < β.normSq := by
  have hNpos : 0 < β.normSq := normSq_pos β hβ
  obtain ⟨qre, rre, heqre, hbre⟩ := centered_div_int_sq (α * β.conj).re β.normSq hNpos
  obtain ⟨qim, rim, heqim, hbim⟩ := centered_div_int_sq (α * β.conj).im β.normSq hNpos
  refine ⟨⟨qre, qim⟩, α - β * ⟨qre, qim⟩, ?_, ?_⟩
  · -- α = βγ + (α − βγ)
    cases α with
    | mk ax ay =>
    cases β with
    | mk bx bz =>
      refine ZOmega.ext ?_ ?_
      · show ax = (bx * qre - bz * qim) + (ax + -(bx * qre - bz * qim))
        ring_intZ
      · show ay = (bx * qim + bz * qre - bz * qim) + (ay + -(bx * qim + bz * qre - bz * qim))
        ring_intZ
  · -- ‖ρ‖² < ‖β‖²
    -- ρ · conj β = ⟨rre, rim⟩
    have hrc : (α - β * ⟨qre, qim⟩) * β.conj = ⟨rre, rim⟩ := by
      rw [rho_conj_eq]
      refine ZOmega.ext ?_ ?_
      · show (α * β.conj).re - qre * β.normSq = rre
        rw [heqre]; ring_intZ
      · show (α * β.conj).im - qim * β.normSq = rim
        rw [heqim]; ring_intZ
    -- ‖ρ‖²·N = rre² − rre·rim + rim²
    have hns : (α - β * ⟨qre, qim⟩).normSq * β.normSq
        = rre * rre - rre * rim + rim * rim := by
      have h1 := normSq_mul (α - β * ⟨qre, qim⟩) β.conj
      rw [normSq_conj, hrc] at h1
      exact h1.symm
    -- covering bound: 8·(‖ρ‖²·N) ≤ 6·N²
    have hbre' : 4 * rre * rre ≤ β.normSq * β.normSq := by
      rw [mul_assoc]; exact hbre
    have hbim' : 4 * rim * rim ≤ β.normSq * β.normSq := by
      rw [mul_assoc]; exact hbim
    have hcov := covering_bound rre rim β.normSq hbre' hbim'
    rw [← hns] at hcov
    -- hcov : 8·(‖ρ‖²·N) ≤ 6·(N·N)
    exact div_step_ineq hNpos hcov

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
