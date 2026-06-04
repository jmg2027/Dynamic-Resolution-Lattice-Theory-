import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIAlgebra213
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.PolyIntMTactic

/-!
# GaussianDivStep — `ℤ[i]` is norm-Euclidean (disc-`−4` analog of `EisensteinDivStep`)

For `β ≠ 0` there is a quotient `γ` whose remainder `ρ = α − βγ` is strictly smaller in norm,
by rounding each coordinate of `α·conj β` to the nearest multiple of `N = ‖β‖²`.  The
Gaussian covering bound is `‖ρ‖²·N = rre² + rim² ≤ N²/2 < N²` (covering radius² = 1/2 < 1).

  * `normSq_conj` / `normSq_pos` — `‖conj u‖² = ‖u‖²`, `β ≠ 0 → 0 < ‖β‖²`.
  * `gaussian_cover` — `4r² ≤ N², 4s² ≤ N² ⟹ 4(r²+s²) ≤ 2N²`.
  * `rho_conj_eq` — `(α − βγ)·conjβ = ⟨(α·conjβ).re − qre·N, (α·conjβ).im − qim·N⟩`.
  * `div_step_ineq` — `4(P·N) ≤ 2N²`, `0 < N` ⟹ `P < N`.
  * ★★★★ `zi_div_step` — `β ≠ 0 → ∃ γ ρ, α = βγ + ρ ∧ ‖ρ‖² < ‖β‖²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int_sq)
open E213.Meta.Int213 (mul_nonneg)
open E213.Meta.Int213.OrderMul
  (mul_le_mul_left_nonneg int_sign mul_pos int_lt_irrefl)
open E213.Meta.Int213.Order
  (lt_of_sub_one_nonneg sub_zero zero_sub ofNat_succ_sub_one le_of_sub_nonneg nonneg_of_le_zero
   le_of_lt lt_of_le_of_lt lt_of_sub_pos sub_pos_of_lt le_trans add_le_add_right add_le_add_left)

/-! ## §1 — ZI helpers -/

/-- `‖conj u‖² = ‖u‖²`. -/
theorem normSq_conj (u : ZI) : (ZI.conj u).normSq = u.normSq := by
  cases u with
  | mk p q =>
    show p * p + (-q) * (-q) = p * p + q * q
    ring_intZ

/-- `β ≠ 0 → 0 < ‖β‖²`. -/
theorem normSq_pos (β : ZI) (hβ : β ≠ 0) : 0 < β.normSq := by
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

/-- The Gaussian covering bound: `4r² ≤ N²` and `4s² ≤ N²` ⟹ `4(r²+s²) ≤ 2N²`. -/
theorem gaussian_cover (x y N : Int) (hx : 4 * (x * x) ≤ N * N) (hy : 4 * (y * y) ≤ N * N) :
    4 * (x * x + y * y) ≤ 2 * (N * N) := by
  have h1 : 4 * (x * x) + 4 * (y * y) ≤ N * N + N * N :=
    le_trans (add_le_add_right hx (4 * (y * y))) (add_le_add_left hy (N * N))
  rw [show 4 * (x * x + y * y) = 4 * (x * x) + 4 * (y * y) from by ring_intZ,
      show 2 * (N * N) = N * N + N * N from by ring_intZ]
  exact h1

/-! ## §2 — the remainder identity and the division step -/

/-- `ρ · conj β = ⟨(α·conjβ).re − qre·N, (α·conjβ).im − qim·N⟩`, `ρ = α − βγ`. -/
theorem rho_conj_eq (α β : ZI) (qre qim : Int) :
    (α - β * ⟨qre, qim⟩) * (ZI.conj β)
      = ⟨(α * (ZI.conj β)).re - qre * β.normSq, (α * (ZI.conj β)).im - qim * β.normSq⟩ := by
  cases α with
  | mk ax ay =>
  cases β with
  | mk bx bj =>
    refine ZI.ext ?_ ?_
    · show (ax + -(bx * qre - bj * qim)) * bx - (ay + -(bx * qim + bj * qre)) * (-bj)
         = (ax * bx - ay * (-bj)) - qre * (bx * bx + bj * bj)
      ring_intZ
    · show (ax + -(bx * qre - bj * qim)) * (-bj) + (ay + -(bx * qim + bj * qre)) * bx
         = (ax * (-bj) + ay * bx) - qim * (bx * bx + bj * bj)
      ring_intZ

/-- `4(P·N) ≤ 2N²` with `0 < N` forces `P < N`.  (If `N ≤ P` then `4N² ≤ 4(P·N) ≤ 2N²`, so
    `2N² ≤ 0`, contradicting `0 < N²`.) -/
theorem div_step_ineq {P N : Int} (hNpos : 0 < N)
    (hcov : 4 * (P * N) ≤ 2 * (N * N)) : P < N := by
  rcases int_sign (P - N) with hge | hlt
  · exfalso
    have hNle : N ≤ P := le_of_sub_nonneg (nonneg_of_le_zero hge)
    have h4N : (0 : Int) ≤ 4 * N := mul_nonneg (by decide) (le_of_lt hNpos)
    have hmul : 4 * (N * N) ≤ 4 * (P * N) := by
      have hx := mul_le_mul_left_nonneg hNle (4 * N) h4N
      rw [show (4 * N) * N = 4 * (N * N) from by ring_intZ,
          show (4 * N) * P = 4 * (P * N) from by ring_intZ] at hx
      exact hx
    have hstep : 4 * (N * N) ≤ 2 * (N * N) := le_trans hmul hcov
    have hNN : 0 < N * N := mul_pos hNpos hNpos
    have h2NN : 0 < 2 * (N * N) := mul_pos (by decide) hNN
    have h24 : 2 * (N * N) < 4 * (N * N) := by
      apply lt_of_sub_pos
      rw [show 4 * (N * N) - 2 * (N * N) = 2 * (N * N) from by ring_intZ]
      exact h2NN
    exact int_lt_irrefl (4 * (N * N)) (lt_of_le_of_lt hstep h24)
  · have h2 : 0 < (0 : Int) - (P - N) := sub_pos_of_lt hlt
    rw [zero_sub, show -(P - N) = N - P from by ring_intZ] at h2
    exact lt_of_sub_pos h2

/-- ★★★★ **The `ℤ[i]` division step (norm-Euclidean).**  For `β ≠ 0` there is a quotient `γ`
    with `ρ = α − βγ` strictly smaller in norm: `‖ρ‖² < ‖β‖²`. -/
theorem zi_div_step (α β : ZI) (hβ : β ≠ 0) :
    ∃ γ ρ : ZI, α = β * γ + ρ ∧ ρ.normSq < β.normSq := by
  have hNpos : 0 < β.normSq := normSq_pos β hβ
  obtain ⟨qre, rre, heqre, hbre⟩ := centered_div_int_sq (α * (ZI.conj β)).re β.normSq hNpos
  obtain ⟨qim, rim, heqim, hbim⟩ := centered_div_int_sq (α * (ZI.conj β)).im β.normSq hNpos
  refine ⟨⟨qre, qim⟩, α - β * ⟨qre, qim⟩, ?_, ?_⟩
  · cases α with
    | mk ax ay =>
    cases β with
    | mk bx bj =>
      refine ZI.ext ?_ ?_
      · show ax = (bx * qre - bj * qim) + (ax + -(bx * qre - bj * qim))
        ring_intZ
      · show ay = (bx * qim + bj * qre) + (ay + -(bx * qim + bj * qre))
        ring_intZ
  · -- ρ · conj β = ⟨rre, rim⟩
    have hrc : (α - β * ⟨qre, qim⟩) * (ZI.conj β) = ⟨rre, rim⟩ := by
      rw [rho_conj_eq]
      refine ZI.ext ?_ ?_
      · show (α * (ZI.conj β)).re - qre * β.normSq = rre
        rw [heqre]; ring_intZ
      · show (α * (ZI.conj β)).im - qim * β.normSq = rim
        rw [heqim]; ring_intZ
    -- ‖ρ‖²·N = rre² + rim²
    have hns : (α - β * ⟨qre, qim⟩).normSq * β.normSq = rre * rre + rim * rim := by
      have h1 := normSq_mul (α - β * ⟨qre, qim⟩) (ZI.conj β)
      rw [normSq_conj, hrc] at h1
      exact h1.symm
    -- covering: 4(‖ρ‖²·N) ≤ 2N²
    have hcov := gaussian_cover rre rim β.normSq hbre hbim
    rw [← hns] at hcov
    exact div_step_ineq hNpos hcov

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep
