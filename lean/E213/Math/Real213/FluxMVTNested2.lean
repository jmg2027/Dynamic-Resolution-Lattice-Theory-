import E213.Math.Real213.FluxMVTNested

/-!
# Research.Real213FluxMVTNested2

Phase CJ: more nested midpoint MVT witnesses.

Math: f(x) = mid(mid(x, x²), x²) = (x + 3x²)/4.
- f(0) = 0, f(1) = 1, passthrough.
- f'(x) = (1 + 6x)/4. = 1 when 6x = 3 → x = 1/2 dyadic.
-/

namespace E213.Math.Real213.FluxMVTNested2

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.HasDyadicMVTWitness
  (HasDyadicMVTWitness HasDyadicMVTWitness_at)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness (mvt_exists)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Math.Real213.FluxMVTWitness
  (squareDerivative_at_half squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore
  (mid_id_square_derivative_at_half mid_id_square_derivative_at_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut cutMid_self_constCut_at)

/-- ★ d/dx [mid(mid(x, x²), x²)] at x = 1/2 = 1. -/
theorem mid_mid_id_square_square_derivative_at_half :
    (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2)
      = constCut 1 1 := by
  show cutMid ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              (squareIsDifferentiable.derivative (constCut 1 2))
       = constCut 1 1
  rw [mid_id_square_derivative_at_half, squareDerivative_at_half]
  exact cutMid_self_constCut 1 1 (by decide)

/-- HasDyadicMVTWitness for mid(mid(x, x²), x²). -/
def HasDyadicMVTWitness.mid_mid_id_square_square :
    HasDyadicMVTWitness (midIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
      squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof := mid_mid_id_square_square_derivative_at_half }

/-- ★ Phase CJ: existential witness for mid(mid(x, x²), x²). -/
theorem mid_mid_id_square_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            squareIsDifferentiable).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists
    HasDyadicMVTWitness.mid_mid_id_square_square

/-- Phase CJ capstone. -/
theorem mid_mid_id_square_square_capstone :
    (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2)
        = constCut 1 1
    ∧ (∃ c, (midIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
              squareIsDifferentiable).derivative c = constCut 1 1) :=
  ⟨mid_mid_id_square_square_derivative_at_half,
   mid_mid_id_square_square_has_dyadic_witness⟩

/-- ★ d/dx [mid(mid(x,x²), x²)] at 1/2 = 1, pointwise (PURE). -/
theorem mid_mid_id_square_square_derivative_at_half_at (m k : Nat) :
    (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2) m k
      = constCut 1 1 m k := by
  show cutMid ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              (squareIsDifferentiable.derivative (constCut 1 2)) m k
       = constCut 1 1 m k
  show E213.Math.Real213.CutSum.cutSumAux
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              (squareIsDifferentiable.derivative (constCut 1 2))
              k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
  have step :
      E213.Math.Real213.CutSum.cutSumAux
            ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative (constCut 1 2))
            (squareIsDifferentiable.derivative (constCut 1 2))
            k (2*(2*m)) (2*(2*m))
      = E213.Math.Real213.CutSum.cutSumAux (constCut 1 1) (constCut 1 1)
            k (2*(2*m)) (2*(2*m)) :=
    E213.Math.Real213.CutSumDetermined.cutSumAux_congr k (2*(2*m))
      ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2)) (constCut 1 1)
      (squareIsDifferentiable.derivative (constCut 1 2)) (constCut 1 1)
      (fun m' _ => mid_id_square_derivative_at_half_at m' (2*k))
      (fun m' _ => squareDerivative_at_half_at m' (2*k))
      (2*(2*m)) (Nat.le_refl _)
  rw [step]
  show cutMid (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _)

/-- HasDyadicMVTWitness_at for mid(mid(x,x²), x²) — PURE. -/
def HasDyadicMVTWitness_at.mid_mid_id_square_square_at :
    HasDyadicMVTWitness_at (midIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
      squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof_at := mid_mid_id_square_square_derivative_at_half_at }

/-- ★ Phase CJ _at: existential witness (PURE). -/
theorem mid_mid_id_square_square_has_dyadic_witness_at :
    ∃ c, ∀ m k, (midIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            squareIsDifferentiable).derivative c m k = constCut 1 1 m k :=
  mvt_exists_at HasDyadicMVTWitness_at.mid_mid_id_square_square_at

/-- Phase CJ _at capstone (PURE). -/
theorem mid_mid_id_square_square_capstone_at :
    (∀ m k, (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2) m k
            = constCut 1 1 m k)
    ∧ (∃ c, ∀ m k, (midIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
              squareIsDifferentiable).derivative c m k = constCut 1 1 m k) :=
  ⟨mid_mid_id_square_square_derivative_at_half_at,
   mid_mid_id_square_square_has_dyadic_witness_at⟩

end E213.Math.Real213.FluxMVTNested2
