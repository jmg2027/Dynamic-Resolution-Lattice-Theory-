import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtAlgebra213
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.PolyIntMTactic

/-!
# ZSqrtNegDivStep — `ℤ[√−D]` is norm-Euclidean for `1 ≤ D ≤ 2` (parametric descent)

The parametric generalisation of `GaussianDivStep` over the radicand: `ZSqrt D` carries the
norm `‖u‖² = re² + D·im²` (so `ZSqrt 1 = ℤ[i]`, `ZSqrt 2 = ℤ[√−2]`).  Rounding each coordinate
of `α·conj β` against `N = ‖β‖²` gives `‖ρ‖²·N = rre² + D·rim² ≤ (1+D)N²/4 < N²` whenever
`D ≤ 2` (covering radius² `(1+D)/4`).

  * `cover` — `4r² ≤ N², 4s² ≤ N²` ⟹ `4(r² + D·s²) ≤ (1+D)·N²`.
  * `div_step_ineq` — `4(P·N) ≤ (1+D)N²`, `0 < N`, `D ≤ 2` ⟹ `P < N`.
  * ★★★★ `zsqrt_div_step` — `1 ≤ D ≤ 2`, `β ≠ 0` ⟹ `∃ γ ρ, α = βγ + ρ ∧ ‖ρ‖² < ‖β‖²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegDivStep

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt (ZSqrt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt.ZSqrt
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int_sq)
open E213.Meta.Int213 (mul_nonneg)
open E213.Meta.Int213.OrderMul
  (mul_le_mul_left_nonneg int_sign mul_pos int_lt_irrefl)
open E213.Meta.Int213.Order
  (lt_of_sub_one_nonneg sub_zero zero_sub ofNat_succ_sub_one le_of_sub_nonneg nonneg_of_le_zero
   le_of_lt lt_of_le_of_lt lt_of_lt_of_le lt_of_sub_pos sub_pos_of_lt le_trans
   add_le_add_right add_le_add_left)

/-- `‖conj u‖² = ‖u‖²`. -/
theorem normSq_conj {D : Int} (u : ZSqrt D) : (ZSqrt.conj u).normSq = u.normSq := by
  cases u with
  | mk p q =>
    show p * p + D * ((-q) * (-q)) = p * p + D * (q * q)
    ring_intZ

/-- `β ≠ 0 → 0 < ‖β‖²` (for `0 < D`). -/
theorem normSq_pos {D : Int} (hD : 0 < D) (β : ZSqrt D) (hβ : β ≠ 0) : 0 < β.normSq := by
  have hne : β.normSq ≠ 0 := fun h => hβ ((normSq_eq_zero_iff hD β).mp h)
  have hnn : 0 ≤ β.normSq := normSq_nonneg (le_of_lt hD) β
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

/-- The covering bound: `4r² ≤ N²`, `4s² ≤ N²`, `0 ≤ D` ⟹ `4(r² + D·s²) ≤ (1+D)·N²`. -/
theorem cover (D x y N : Int) (hD : 0 ≤ D) (hx : 4 * (x * x) ≤ N * N) (hy : 4 * (y * y) ≤ N * N) :
    4 * (x * x + D * (y * y)) ≤ (1 + D) * (N * N) := by
  have hDy : D * (4 * (y * y)) ≤ D * (N * N) := mul_le_mul_left_nonneg hy D hD
  have h1 : 4 * (x * x) + D * (4 * (y * y)) ≤ N * N + D * (N * N) :=
    le_trans (add_le_add_right hx (D * (4 * (y * y)))) (add_le_add_left hDy (N * N))
  rw [show 4 * (x * x + D * (y * y)) = 4 * (x * x) + D * (4 * (y * y)) from by ring_intZ,
      show (1 + D) * (N * N) = N * N + D * (N * N) from by ring_intZ]
  exact h1

/-- The remainder identity `ρ · conj β = ⟨(α·conjβ).re − qre·N, (α·conjβ).im − qim·N⟩`. -/
theorem rho_conj_eq {D : Int} (α β : ZSqrt D) (qre qim : Int) :
    (α - β * ⟨qre, qim⟩) * (ZSqrt.conj β)
      = ⟨(α * (ZSqrt.conj β)).re - qre * β.normSq,
          (α * (ZSqrt.conj β)).im - qim * β.normSq⟩ := by
  cases α with
  | mk ax ay =>
  cases β with
  | mk bx bj =>
    refine ZSqrt.ext ?_ ?_
    · show (ax + -(bx * qre - D * (bj * qim))) * bx
            - D * ((ay + -(bx * qim + bj * qre)) * (-bj))
         = (ax * bx - D * (ay * (-bj))) - qre * (bx * bx + D * (bj * bj))
      ring_intZ
    · show (ax + -(bx * qre - D * (bj * qim))) * (-bj)
            + (ay + -(bx * qim + bj * qre)) * bx
         = (ax * (-bj) + ay * bx) - qim * (bx * bx + D * (bj * bj))
      ring_intZ

/-- `4(P·N) ≤ (1+D)N²` with `0 < N` and `D ≤ 2` forces `P < N`. -/
theorem div_step_ineq {D P N : Int} (hNpos : 0 < N) (hD2 : D ≤ 2)
    (hcov : 4 * (P * N) ≤ (1 + D) * (N * N)) : P < N := by
  rcases int_sign (P - N) with hge | hlt
  · exfalso
    have hNle : N ≤ P := le_of_sub_nonneg (nonneg_of_le_zero hge)
    have h4N : (0 : Int) ≤ 4 * N := mul_nonneg (by decide) (le_of_lt hNpos)
    have hmul : 4 * (N * N) ≤ 4 * (P * N) := by
      have hx := mul_le_mul_left_nonneg hNle (4 * N) h4N
      rw [show (4 * N) * N = 4 * (N * N) from by ring_intZ,
          show (4 * N) * P = 4 * (P * N) from by ring_intZ] at hx
      exact hx
    -- (1+D)N² ≤ 3N² since D ≤ 2
    have hNN : 0 < N * N := mul_pos hNpos hNpos
    have h1D3 : (1 + D) * (N * N) ≤ 3 * (N * N) := by
      have hd3 : 1 + D ≤ 3 := by
        have := add_le_add_left hD2 1
        rw [show (1 : Int) + 2 = 3 from by decide] at this
        exact this
      have hx := mul_le_mul_left_nonneg hd3 (N * N) (le_of_lt hNN)
      rw [E213.Meta.Int213.mul_comm (N * N) (1 + D),
          E213.Meta.Int213.mul_comm (N * N) 3] at hx
      exact hx
    have hstep : 4 * (N * N) ≤ 3 * (N * N) := le_trans (le_trans hmul hcov) h1D3
    have h34 : 3 * (N * N) < 4 * (N * N) := by
      apply lt_of_sub_pos
      rw [show 4 * (N * N) - 3 * (N * N) = N * N from by ring_intZ]
      exact hNN
    exact int_lt_irrefl (4 * (N * N)) (lt_of_le_of_lt hstep h34)
  · have h2 : 0 < (0 : Int) - (P - N) := sub_pos_of_lt hlt
    rw [zero_sub, show -(P - N) = N - P from by ring_intZ] at h2
    exact lt_of_sub_pos h2

/-- ★★★★ **`ℤ[√−D]` is norm-Euclidean for `1 ≤ D ≤ 2`.**  For `β ≠ 0`, a quotient `γ` with
    `ρ = α − βγ` strictly smaller in norm. -/
theorem zsqrt_div_step {D : Int} (hD1 : 1 ≤ D) (hD2 : D ≤ 2) (α β : ZSqrt D) (hβ : β ≠ 0) :
    ∃ γ ρ : ZSqrt D, α = β * γ + ρ ∧ ρ.normSq < β.normSq := by
  have hDpos : 0 < D := lt_of_lt_of_le (by decide) hD1
  have hNpos : 0 < β.normSq := normSq_pos hDpos β hβ
  obtain ⟨qre, rre, heqre, hbre⟩ := centered_div_int_sq (α * (ZSqrt.conj β)).re β.normSq hNpos
  obtain ⟨qim, rim, heqim, hbim⟩ := centered_div_int_sq (α * (ZSqrt.conj β)).im β.normSq hNpos
  refine ⟨⟨qre, qim⟩, α - β * ⟨qre, qim⟩, ?_, ?_⟩
  · cases α with
    | mk ax ay =>
    cases β with
    | mk bx bj =>
      refine ZSqrt.ext ?_ ?_
      · show ax = (bx * qre - D * (bj * qim)) + (ax + -(bx * qre - D * (bj * qim)))
        ring_intZ
      · show ay = (bx * qim + bj * qre) + (ay + -(bx * qim + bj * qre))
        ring_intZ
  · have hrc : (α - β * ⟨qre, qim⟩) * (ZSqrt.conj β) = ⟨rre, rim⟩ := by
      rw [rho_conj_eq]
      refine ZSqrt.ext ?_ ?_
      · show (α * (ZSqrt.conj β)).re - qre * β.normSq = rre
        rw [heqre]; ring_intZ
      · show (α * (ZSqrt.conj β)).im - qim * β.normSq = rim
        rw [heqim]; ring_intZ
    have hns : (α - β * ⟨qre, qim⟩).normSq * β.normSq = rre * rre + D * (rim * rim) := by
      have h1 := normSq_mul (α - β * ⟨qre, qim⟩) (ZSqrt.conj β)
      rw [normSq_conj, hrc] at h1
      exact h1.symm
    have hcov := cover D rre rim β.normSq (le_of_lt hDpos) hbre hbim
    rw [← hns] at hcov
    exact div_step_ineq hNpos hD2 hcov

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegDivStep
