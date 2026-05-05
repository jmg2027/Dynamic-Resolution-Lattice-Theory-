import E213.Math.Real213.CutSumOne
import E213.Math.Real213.HasDyadicMVTWitness
import E213.Math.Real213.ClassicCalcCombinators

/-!
# Constructive dyadic MVT witnesses at `c = 1/2`

Functions buildable from `{id, x², mid}` combinators all admit a
*dyadic* (constructively rational) witness for the Mean Value Theorem
at the point `c = 1/2 = constCut 1 2`.  Key reduction: `cutMid X X = X`
for constant cuts, plus the constCut algebra of cutSum/cutMul.

| function                            | witness | derivative at 1/2 |
|-------------------------------------|---------|-------------------|
| `x²`                                | 1/2     | 1                 |
| `mid(x, x²) = (x+x²)/2`             | 1/2     | 1                 |
| `mid(x, mid(x, x²)) = (3x+x²)/4`    | 1/2     | 1                 |
| `mid(mid(x,x²), x²) = (x+3x²)/4`    | 1/2     | 1                 |

Sub-namespaces preserved (cross-file `open` declarations stay valid):

  * `E213.Math.Real213.FluxMVTWitness`  — base (x²)
  * `E213.Math.Real213.FluxMVTMore`     — mid(x, x²)
  * `E213.Math.Real213.FluxMVTNested`   — mid(x, mid(x, x²))
  * `E213.Math.Real213.FluxMVTNested2`  — mid(mid(x, x²), x²)

(Consolidated 2026-05-05 from 5 phase files: FluxMVTWitness [Phase BR]
+ FluxMVTMore [Phase BU] + FluxMVTNested [Phase CF] + FluxMVTNested2
[Phase CJ] + FluxMVTPattern [Phase CG capstone — DELETED, was pure
bundle].  Per-stage capstone bundles dropped.)
-/

namespace E213.Math.Real213.FluxMVTWitness

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.IsDifferentiable (IsDifferentiable)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutMulOne
  (cutMul_one_const_at cutMul_const_one_at)
open E213.Math.Real213.CutSumOne (cutSum_half_half_at)
open E213.Math.Real213.CutSumDetermined (cutSumAux_congr)
open E213.Math.Real213.FluxMVTPolynomial.FluxCut
  (mvt_square_unitBracket_pure)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq)

/-- d/dx [x²] at x = 1/2 = 1 (pointwise, ∅-axiom). -/
theorem squareDerivative_at_half_at (m k : Nat) :
    squareIsDifferentiable.derivative (constCut 1 2) m k = constCut 1 1 m k := by
  show cutSum (cutMul (constCut 1 1) (constCut 1 2))
              (cutMul (constCut 1 2) (constCut 1 1)) m k
       = constCut 1 1 m k
  show cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                 (cutMul (constCut 1 2) (constCut 1 1)) k (2*m) (2*m)
       = constCut 1 1 m k
  have step :
      cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                (cutMul (constCut 1 2) (constCut 1 1)) k (2*m) (2*m)
      = cutSumAux (constCut 1 2) (constCut 1 2) k (2*m) (2*m) :=
    cutSumAux_congr k (2*m)
      (cutMul (constCut 1 1) (constCut 1 2)) (constCut 1 2)
      (cutMul (constCut 1 2) (constCut 1 1)) (constCut 1 2)
      (fun m' _ => cutMul_one_const_at 1 2 m' (2*k))
      (fun m' _ => cutMul_const_one_at 1 2 m' (2*k))
      (2*m) (Nat.le_refl _)
  rw [step]
  exact cutSum_half_half_at m k

/-- The witness c = 1/2 is interior to [0, 1]. -/
theorem mvt_square_witness_in_interior :
    (constCut 1 2 : Nat → Nat → Bool) 1 2 = true := by decide

/-- MVT for x² with explicit dyadic witness c = 1/2 (PURE). -/
theorem mvt_square_explicit_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
                = constCut 1 1 m k) :=
  ⟨mvt_square_unitBracket_pure, squareDerivative_at_half_at⟩

/-- MVT existence (pointwise) with explicit witness for x² (PURE). -/
theorem mvt_square_explicit_witness_at :
    ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨constCut 1 2, squareDerivative_at_half_at⟩

end E213.Math.Real213.FluxMVTWitness

namespace E213.Math.Real213.FluxMVTMore

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.HasDyadicMVTWitness
  (HasDyadicMVTWitness_at square_has_dyadic_witness_at)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutMulOne
  (cutMul_one_const_at cutMul_const_one_at)
open E213.Math.Real213.CutSumOne (cutSum_half_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)
open E213.Math.Real213.CutSumDetermined (cutSumAux_congr)

/-- d/dx [(x + x²)/2] at x = 1/2 = 1 (pointwise, ∅-axiom). -/
theorem mid_id_square_derivative_at_half_at (m k : Nat) :
    (midIsDifferentiable idIsDifferentiable squareIsDifferentiable).derivative
        (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMid (constCut 1 1)
              (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                      (cutMul (constCut 1 2) (constCut 1 1))) m k
       = constCut 1 1 m k
  show cutSum (constCut 1 1)
              (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                      (cutMul (constCut 1 2) (constCut 1 1))) (2*m) k
       = constCut 1 1 m k
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
  show cutMid (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _)

/-- HasDyadicMVTWitness_at instance for mid(x, x²) (PURE). -/
def HasDyadicMVTWitness_at.mid_id_square_at :
    HasDyadicMVTWitness_at (midIsDifferentiable idIsDifferentiable
                            squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof_at := mid_id_square_derivative_at_half_at }

/-- mid(x, x²) has constructive MVT existence (PURE _at). -/
theorem mid_id_square_has_dyadic_witness_at :
    ∃ c, ∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                  ).derivative c m k = constCut 1 1 m k :=
  mvt_exists_at HasDyadicMVTWitness_at.mid_id_square_at

end E213.Math.Real213.FluxMVTMore

namespace E213.Math.Real213.FluxMVTNested

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.HasDyadicMVTWitness (HasDyadicMVTWitness_at)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)

/-- d/dx [mid(x, mid(x, x²))] at x = 1/2 = 1 (pointwise PURE). -/
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

/-- HasDyadicMVTWitness_at for nested mid (PURE). -/
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

end E213.Math.Real213.FluxMVTNested

namespace E213.Math.Real213.FluxMVTNested2

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances (squareIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.HasDyadicMVTWitness (HasDyadicMVTWitness_at)
open E213.Math.Real213.HasDyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)

/-- d/dx [mid(mid(x,x²), x²)] at x = 1/2 = 1 (pointwise PURE). -/
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

/-- HasDyadicMVTWitness_at for mid(mid(x,x²), x²) (PURE). -/
def HasDyadicMVTWitness_at.mid_mid_id_square_square_at :
    HasDyadicMVTWitness_at (midIsDifferentiable
      (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
      squareIsDifferentiable) :=
  { witness := constCut 1 2
    proof_at := mid_mid_id_square_square_derivative_at_half_at }

/-- Existential witness (PURE _at). -/
theorem mid_mid_id_square_square_has_dyadic_witness_at :
    ∃ c, ∀ m k, (midIsDifferentiable
            (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            squareIsDifferentiable).derivative c m k = constCut 1 1 m k :=
  mvt_exists_at HasDyadicMVTWitness_at.mid_mid_id_square_square_at

end E213.Math.Real213.FluxMVTNested2
