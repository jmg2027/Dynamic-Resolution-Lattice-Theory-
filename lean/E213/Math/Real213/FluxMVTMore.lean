import E213.Math.Real213.HasDyadicMVTWitness

/-!
# Research.Real213FluxMVTMore

Phase BU: more dyadic MVT witnesses.  Shows that the dyadic-witness
class is non-trivially populated beyond x².

  mid(x, x²) at c = 1/2 : derivative = 1 (propEq)
  HasDyadicMVTWitness.mid_id_square : new instance

Mathematical observation: f(x) = (x + x²)/2 has derivative (1+2x)/2,
which equals 1 when x = 1/2.  Witness c = 1/2 dyadic.
-/

namespace E213.Math.Real213.FluxMVTMore

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.HasDyadicMVTWitness
  (HasDyadicMVTWitness_at square_has_dyadic_witness_at)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Math.Real213.FluxMVTWitness
  (squareDerivative_at_half_at)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutMulOne
  (cutMul_one_const_at cutMul_const_one_at)
open E213.Math.Real213.CutSumOne (cutSum_half_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)
open E213.Math.Real213.CutSumDetermined (cutSumAux_congr)

/-- ★ d/dx [(x + x²)/2] at x = 1/2 = 1 — pointwise (∅-axiom). -/
theorem mid_id_square_derivative_at_half_at (m k : Nat) :
    (midIsDifferentiable idIsDifferentiable squareIsDifferentiable).derivative
        (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMid (constCut 1 1)
              (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                      (cutMul (constCut 1 2) (constCut 1 1))) m k
       = constCut 1 1 m k
  -- cutMid X Y m k = cutSum X Y (2*m) k
  show cutSum (constCut 1 1)
              (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                      (cutMul (constCut 1 2) (constCut 1 1))) (2*m) k
       = constCut 1 1 m k
  -- Push pointwise eq through outer cutSumAux: swap inner cutSum to constCut 1 1.
  show cutSumAux (constCut 1 1)
                 (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                         (cutMul (constCut 1 2) (constCut 1 1)))
                 k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
  have step :
      cutSumAux (constCut 1 1)
                (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                        (cutMul (constCut 1 2) (constCut 1 1)))
                k (2*(2*m)) (2*(2*m))
      = cutSumAux (constCut 1 1) (constCut 1 1) k (2*(2*m)) (2*(2*m)) :=
    cutSumAux_congr k (2*(2*m))
      (constCut 1 1) (constCut 1 1)
      (cutSum (cutMul (constCut 1 1) (constCut 1 2))
              (cutMul (constCut 1 2) (constCut 1 1)))
      (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => by
        -- Show cutSum (cutMul ... ) (cutMul ...) m' (2*k) = constCut 1 1 m' (2*k)
        -- via inner cutSumAux_congr + cutSum_half_half_at.
        show cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                       (cutMul (constCut 1 2) (constCut 1 1))
                       (2*k) (2*m') (2*m') = constCut 1 1 m' (2*k)
        have inner :
            cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                      (cutMul (constCut 1 2) (constCut 1 1))
                      (2*k) (2*m') (2*m')
            = cutSumAux (constCut 1 2) (constCut 1 2)
                      (2*k) (2*m') (2*m') :=
          cutSumAux_congr (2*k) (2*m')
            (cutMul (constCut 1 1) (constCut 1 2)) (constCut 1 2)
            (cutMul (constCut 1 2) (constCut 1 1)) (constCut 1 2)
            (fun m'' _ => cutMul_one_const_at 1 2 m'' (2*(2*k)))
            (fun m'' _ => cutMul_const_one_at 1 2 m'' (2*(2*k)))
            (2*m') (Nat.le_refl _)
        rw [inner]
        exact cutSum_half_half_at m' (2*k))
      (2*(2*m)) (Nat.le_refl _)
  rw [step]
  -- Goal: cutSumAux (constCut 1 1) (constCut 1 1) k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
  -- = cutSum (constCut 1 1) (constCut 1 1) (2*m) k
  -- = cutMid (constCut 1 1) (constCut 1 1) m k
  show cutMid (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _)

/-- HasDyadicMVTWitness_at instance for mid(x, x²) — PURE pointwise. -/
def HasDyadicMVTWitness_at.mid_id_square_at :
    HasDyadicMVTWitness_at (midIsDifferentiable idIsDifferentiable
                            squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof_at := mid_id_square_derivative_at_half_at }

/-- mid(x, x²) has constructive MVT existence (PURE _at form). -/
theorem mid_id_square_has_dyadic_witness_at :
    ∃ c, ∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                  ).derivative c m k = constCut 1 1 m k :=
  mvt_exists_at HasDyadicMVTWitness_at.mid_id_square_at

/-- ★ Phase BU _at capstone (PURE).  Pointwise variants of the
    extended MVT-witness bundle. -/
theorem mvt_witness_extended_capstone_at :
    (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
              = constCut 1 1 m k)
    ∧ (∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2) m k = constCut 1 1 m k)
    ∧ (∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k)
    ∧ (∃ c, ∀ m k, (midIsDifferentiable idIsDifferentiable
                    squareIsDifferentiable).derivative c m k
                  = constCut 1 1 m k) :=
  ⟨squareDerivative_at_half_at,
   mid_id_square_derivative_at_half_at,
   square_has_dyadic_witness_at,
   mid_id_square_has_dyadic_witness_at⟩

end E213.Math.Real213.FluxMVTMore
