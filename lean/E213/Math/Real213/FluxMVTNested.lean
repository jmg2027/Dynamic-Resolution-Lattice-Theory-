import E213.Math.Real213.ClassicCalcCombinators
import E213.Math.Real213.HasDyadicMVTWitness

/-!
# Research.Real213FluxMVTNested

Phase CF: nested midpoint MVT witness chain.

Math: f(x) = (3x + x²)/4 = mid(x, mid(x, x²)).
- f(0) = 0, f(1) = 1, passthrough.
- f'(x) = (3 + 2x)/4. = 1 when 2x = 1 → x = 1/2 dyadic.

Witness c = 1/2 propagates through nested mid combinators.
-/

namespace E213.Math.Real213.FluxMVTNested

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
open E213.Math.Real213.FluxMVTMore
  (mid_id_square_derivative_at_half mid_id_square_derivative_at_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut cutMid_self_constCut_at)

/-- ★ d/dx [mid(x, mid(x, x²))] at x = 1/2 = 1 propEq. -/
theorem mid_id_mid_id_square_derivative_at_half :
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) = constCut 1 1 := by
  show cutMid (idIsDifferentiable.derivative (constCut 1 2))
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) = constCut 1 1
  show cutMid (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) = constCut 1 1
  rw [mid_id_square_derivative_at_half]
  exact cutMid_self_constCut 1 1 (by decide)

/-- HasDyadicMVTWitness instance for mid(id, mid(id, x²)). -/
def HasDyadicMVTWitness.mid_id_mid_id_square :
    HasDyadicMVTWitness (midIsDifferentiable idIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)) :=
  { witness := constCut 1 2
    proof := mid_id_mid_id_square_derivative_at_half }

/-- mid(id, mid(id, x²)) has constructive MVT existence. -/
theorem mid_id_mid_id_square_has_dyadic_witness :
    ∃ c, (midIsDifferentiable idIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              )).derivative c = constCut 1 1 :=
  HasDyadicMVTWitness.mvt_exists HasDyadicMVTWitness.mid_id_mid_id_square

/-- Phase CF capstone: nested mid witness chain. -/
theorem nested_mid_witness_capstone :
    -- (1) explicit witness
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) = constCut 1 1
    -- (2) MVT existence (constructive)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                )).derivative c = constCut 1 1) :=
  ⟨mid_id_mid_id_square_derivative_at_half,
   mid_id_mid_id_square_has_dyadic_witness⟩

/-- ★ d/dx [mid(x, mid(x, x²))] at x = 1/2 = 1, pointwise (PURE). -/
theorem mid_id_mid_id_square_derivative_at_half_at (m k : Nat) :
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMid (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) m k = constCut 1 1 m k
  show E213.Math.Real213.CutSum.cutSum (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) (2*m) k = constCut 1 1 m k
  -- Use cutSumAux_congr to substitute the inner derivative pointwise.
  show E213.Math.Real213.CutSum.cutSumAux (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
  have step :
      E213.Math.Real213.CutSum.cutSumAux (constCut 1 1)
            ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative (constCut 1 2))
            k (2*(2*m)) (2*(2*m))
      = E213.Math.Real213.CutSum.cutSumAux (constCut 1 1) (constCut 1 1)
            k (2*(2*m)) (2*(2*m)) :=
    E213.Math.Real213.CutSumDetermined.cutSumAux_congr k (2*(2*m))
      (constCut 1 1) (constCut 1 1)
      ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2)) (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => mid_id_square_derivative_at_half_at m' (2*k))
      (2*(2*m)) (Nat.le_refl _)
  rw [step]
  show cutMid (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _)

/-- HasDyadicMVTWitness_at instance for nested mid (PURE). -/
def HasDyadicMVTWitness_at.mid_id_mid_id_square_at :
    HasDyadicMVTWitness_at (midIsDifferentiable idIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)) :=
  { witness := constCut 1 2
    proof_at := mid_id_mid_id_square_derivative_at_half_at }

/-- mid(id, mid(id, x²)) has constructive MVT existence (PURE _at). -/
theorem mid_id_mid_id_square_has_dyadic_witness_at :
    ∃ c, ∀ m k, (midIsDifferentiable idIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              )).derivative c m k = constCut 1 1 m k :=
  mvt_exists_at HasDyadicMVTWitness_at.mid_id_mid_id_square_at

/-- Phase CF _at capstone (PURE). -/
theorem nested_mid_witness_capstone_at :
    (∀ m k, (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) m k = constCut 1 1 m k)
    ∧ (∃ c, ∀ m k, (midIsDifferentiable idIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                )).derivative c m k = constCut 1 1 m k) :=
  ⟨mid_id_mid_id_square_derivative_at_half_at,
   mid_id_mid_id_square_has_dyadic_witness_at⟩

end E213.Math.Real213.FluxMVTNested
