import E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness
import E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness
import E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum
import E213.Lib.Math.Analysis.Differentiation.DifferentiableMid

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Lattice.CutMidSelf
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumDetermined
import E213.Lib.Math.Real213.Sum.CutSumOne
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# Constructive dyadic MVT witnesses — combinator chain at `c = 1/2`

Continues `FluxMVTWitness.lean` (base x²) up the combinator chain
through `HasDyadicMVTWitness_at` instances:

  | function                              | namespace          |
  |---------------------------------------|--------------------|
  | `mid(x, x²) = (x + x²)/2`             | `FluxMVTMore`      |
  | `mid(x, mid(x, x²)) = (3x + x²)/4`    | `FluxMVTNested`    |
  | `mid(mid(x, x²), x²) = (x + 3x²)/4`   | `FluxMVTNested2`   |

Each derivative is `1` at `c = 1/2`, so each function admits a
`HasDyadicMVTWitness_at` instance.

(Sub-namespaces preserved from /CF/CJ.)
-/
namespace E213.Lib.Math.Analysis.FluxMVTMore

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutMid)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness
  (HasDyadicMVTWitness_at square_has_dyadic_witness_at)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Lib.Math.Real213.Sum.CutSum (cutSumAux)
open E213.Lib.Math.Real213.Mul.CutMulOne
  (cutMul_one_const_at cutMul_const_one_at)
open E213.Lib.Math.Real213.Sum.CutSumOne (cutSum_half_half_at)
open E213.Lib.Math.Real213.Lattice.CutMidSelf (cutMid_self_constCut_at)
open E213.Lib.Math.Real213.Sum.CutSumDetermined (cutSumAux_congr)

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
  rw [E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum.cutSumAux_unitBracket_reduce_at
        (constCut 1 1)
        (cutSum (cutMul (constCut 1 1) (constCut 1 2))
                (cutMul (constCut 1 2) (constCut 1 1)))
        (constCut 1 1) (constCut 1 1) k (2*(2*m))
        (fun _ _ => rfl)
        (fun m' _ => by
          show cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                         (cutMul (constCut 1 2) (constCut 1 1))
                         (2*k) (2*m') (2*m') = constCut 1 1 m' (2*k)
          rw [E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum.cutSumAux_unitBracket_reduce_at
                (cutMul (constCut 1 1) (constCut 1 2))
                (cutMul (constCut 1 2) (constCut 1 1))
                (constCut 1 2) (constCut 1 2) (2*k) (2*m')
                (fun m'' _ => cutMul_one_const_at 1 2 m'' (2*(2*k)))
                (fun m'' _ => cutMul_const_one_at 1 2 m'' (2*(2*k)))]
          exact cutSum_half_half_at m' (2*k))]
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

end E213.Lib.Math.Analysis.FluxMVTMore

namespace E213.Lib.Math.Analysis.FluxMVTNested

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutMid)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness (HasDyadicMVTWitness_at)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Lib.Math.Analysis.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Lib.Math.Real213.Lattice.CutMidSelf (cutMid_self_constCut_at)

/-- d/dx [mid(x, mid(x, x²))] at x = 1/2 = 1 (pointwise PURE). -/
theorem mid_id_mid_id_square_derivative_at_half_at (m k : Nat) :
    (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMid (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) m k = constCut 1 1 m k
  show E213.Lib.Math.Real213.Sum.CutSum.cutSum (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2)) (2*m) k = constCut 1 1 m k
  show E213.Lib.Math.Real213.Sum.CutSum.cutSumAux (constCut 1 1)
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
  rw [E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum.cutSumAux_unitBracket_reduce_at
        (constCut 1 1)
        ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
          ).derivative (constCut 1 2))
        (constCut 1 1) (constCut 1 1) k (2*(2*m))
        (fun _ _ => rfl)
        (fun m' _ => mid_id_square_derivative_at_half_at m' (2*k))]
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

end E213.Lib.Math.Analysis.FluxMVTNested

namespace E213.Lib.Math.Analysis.FluxMVTNested2

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutMid)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness (HasDyadicMVTWitness_at)
open E213.Lib.Math.Analysis.FluxMVT.DyadicMVTWitness.HasDyadicMVTWitness_at (mvt_exists_at)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Lib.Math.Analysis.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Lib.Math.Real213.Lattice.CutMidSelf (cutMid_self_constCut_at)

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
  show E213.Lib.Math.Real213.Sum.CutSum.cutSumAux
              ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                ).derivative (constCut 1 2))
              (squareIsDifferentiable.derivative (constCut 1 2))
              k (2*(2*m)) (2*(2*m)) = constCut 1 1 m k
  rw [E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduceSum.cutSumAux_unitBracket_reduce_at
        ((midIsDifferentiable idIsDifferentiable squareIsDifferentiable
          ).derivative (constCut 1 2))
        (squareIsDifferentiable.derivative (constCut 1 2))
        (constCut 1 1) (constCut 1 1) k (2*(2*m))
        (fun m' _ => mid_id_square_derivative_at_half_at m' (2*k))
        (fun m' _ => squareDerivative_at_half_at m' (2*k))]
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

end E213.Lib.Math.Analysis.FluxMVTNested2
