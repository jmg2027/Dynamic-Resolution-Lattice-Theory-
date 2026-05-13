import E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitnessCombinators
import E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness
import E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Lattice.CutMidSelf
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutMulDetermined
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumDetermined
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Analysis.Differentiation.DifferentiableMid
import E213.Lib.Math.Analysis.Differentiation.Differentiable
/-!
# Witness propagation under derivative combinators

If two `IsDifferentiable` functions `f`, `g` both witness derivative `1`
at `c = 1/2`, then so do the combinator-built functions:

  - `mid(f, g)`            (— `mid_witness_propagates_at`)
  - `id ∘ f`               (— `id_compose_witness_propagates_at`)

Sub-namespaces preserved (cross-file `open` declarations stay valid):

  * `E213.Lib.Math.Analysis.FluxMVT.FluxMVTPropagate`         — `mid` propagation
  * `E213.Lib.Math.Analysis.FluxMVTPropagateCompose`  — `id ∘ f` propagation

(Consolidated 2026-05-05 from 2 .  Per-stage capstone
bundles dropped.)
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxMVTPropagate

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutMid)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Lib.Math.Analysis.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Lib.Math.Analysis.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Lib.Math.Real213.Lattice.CutMidSelf (cutMid_self_constCut_at)

/-- Generic mid witness propagation at c = 1/2 (pointwise PURE). -/
theorem mid_witness_propagates_at {f g}
    (sf : IsDifferentiable f) (sg : IsDifferentiable g)
    (hf : ∀ m k, sf.derivative (constCut 1 2) m k = constCut 1 1 m k)
    (hg : ∀ m k, sg.derivative (constCut 1 2) m k = constCut 1 1 m k)
    (m k : Nat) :
    (midIsDifferentiable sf sg).derivative (constCut 1 2) m k
      = constCut 1 1 m k := by
  show cutMid (sf.derivative (constCut 1 2))
              (sg.derivative (constCut 1 2)) m k = constCut 1 1 m k
  show E213.Lib.Math.Real213.Sum.CutSum.cutSum (sf.derivative (constCut 1 2))
                  (sg.derivative (constCut 1 2)) (2*m) k
       = constCut 1 1 m k
  show E213.Lib.Math.Real213.Sum.CutSum.cutSumAux (sf.derivative (constCut 1 2))
                 (sg.derivative (constCut 1 2)) k (2*(2*m)) (2*(2*m))
       = constCut 1 1 m k
  have step :
      E213.Lib.Math.Real213.Sum.CutSum.cutSumAux
                (sf.derivative (constCut 1 2))
                (sg.derivative (constCut 1 2)) k (2*(2*m)) (2*(2*m))
      = E213.Lib.Math.Real213.Sum.CutSum.cutSumAux
                (constCut 1 1) (constCut 1 1) k (2*(2*m)) (2*(2*m)) :=
    E213.Lib.Math.Real213.Sum.CutSumDetermined.cutSumAux_congr k (2*(2*m))
      (sf.derivative (constCut 1 2)) (constCut 1 1)
      (sg.derivative (constCut 1 2)) (constCut 1 1)
      (fun m' _ => hf m' (2*k))
      (fun m' _ => hg m' (2*k))
      (2*(2*m)) (Nat.le_refl _)
  rw [step]
  show cutMid (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _)

end E213.Lib.Math.Analysis.FluxMVT.FluxMVTPropagate

namespace E213.Lib.Math.Analysis.FluxMVTPropagateCompose

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Differentiation.Differentiable
  (IsDifferentiable idIsDifferentiable composeIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableInstances (squareIsDifferentiable)
open E213.Lib.Math.Analysis.Differentiation.DifferentiableMid (midIsDifferentiable)
open E213.Lib.Math.Analysis.FluxMVT.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Lib.Math.Analysis.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Lib.Math.Real213.Mul.CutMulOne (cutMul_one_one_at)
open E213.Lib.Math.Real213.Mul.CutMul (cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutMulDetermined (cutMulOuter_congr)

/-- id-compose witness propagation at c = 1/2 (pointwise PURE).
    For `g ∘ f` via `composeIsDifferentiable f g`, chain rule gives
    `g'(f(x))·f'(x)`.  When `g = id`, `g'(·) = 1`, so derivative = `f'(x)`. -/
theorem id_compose_witness_propagates_at {f} (sf : IsDifferentiable f)
    (hf : ∀ m k, sf.derivative (constCut 1 2) m k = constCut 1 1 m k)
    (m k : Nat) :
    (composeIsDifferentiable sf idIsDifferentiable).derivative
        (constCut 1 2) m k = constCut 1 1 m k := by
  show cutMul (constCut 1 1) (sf.derivative (constCut 1 2)) m k
       = constCut 1 1 m k
  show cutMulOuter (constCut 1 1) (sf.derivative (constCut 1 2))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1) (sf.derivative (constCut 1 2))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (sf.derivative (constCut 1 2)) (constCut 1 1)
      (fun _ _ => rfl) (fun m' _ => hf m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

end E213.Lib.Math.Analysis.FluxMVTPropagateCompose
