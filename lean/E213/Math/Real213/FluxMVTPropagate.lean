import E213.Math.Real213.DifferentiableInstances
import E213.Math.Real213.FluxMVTNested2

/-!
# Research.Real213FluxMVTPropagate

Phase CK: ★ **Generic mid witness propagation** ★

If two IsDifferentiable functions f, g both have derivative = 1
at c = 1/2, then mid(f, g) also has that property.  Single
abstract theorem encapsulates the entire mid combinator chain.

  mid_witness_propagates : both f, g witness at 1/2 → mid(f, g) too
-/

namespace E213.Math.Real213.FluxMVTPropagate

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable mulIsDifferentiable composeIsDifferentiable
   cutPowFnIsDifferentiable)
open E213.Math.Real213.DifferentiableInstances
  (squareIsDifferentiable cubeIsDifferentiable quarticIsDifferentiable
   squareIsDifferentiable_modulus cubeIsDifferentiable_modulus
   quarticIsDifferentiable_modulus
   cutScaleIsDifferentiable cutHalfIsDifferentiable)
open E213.Math.Real213.DifferentiableHigherPow
  (quinticIsDifferentiable sexticIsDifferentiable septicIsDifferentiable
   octicIsDifferentiable
   quinticIsDifferentiable_modulus sexticIsDifferentiable_modulus
   septicIsDifferentiable_modulus octicIsDifferentiable_modulus)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half_at)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half_at)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut_at)

/-- ★ Generic mid witness propagation at c = 1/2, pointwise (PURE). -/
theorem mid_witness_propagates_at {f g}
    (sf : IsDifferentiable f) (sg : IsDifferentiable g)
    (hf : ∀ m k, sf.derivative (constCut 1 2) m k = constCut 1 1 m k)
    (hg : ∀ m k, sg.derivative (constCut 1 2) m k = constCut 1 1 m k)
    (m k : Nat) :
    (midIsDifferentiable sf sg).derivative (constCut 1 2) m k
      = constCut 1 1 m k := by
  show cutMid (sf.derivative (constCut 1 2))
              (sg.derivative (constCut 1 2)) m k = constCut 1 1 m k
  -- We need: cutMid (sf.derivative ...) (sg.derivative ...) m k = constCut 1 1 m k
  -- Using cutMid X Y m k = cutSum X Y (2*m) k, and cutSumAux_congr to reduce
  -- both inner derivatives to constCut 1 1 pointwise.
  show E213.Math.Real213.CutSum.cutSum (sf.derivative (constCut 1 2))
                  (sg.derivative (constCut 1 2)) (2*m) k
       = constCut 1 1 m k
  show E213.Math.Real213.CutSum.cutSumAux (sf.derivative (constCut 1 2))
                 (sg.derivative (constCut 1 2)) k (2*(2*m)) (2*(2*m))
       = constCut 1 1 m k
  have step :
      E213.Math.Real213.CutSum.cutSumAux
                (sf.derivative (constCut 1 2))
                (sg.derivative (constCut 1 2)) k (2*(2*m)) (2*(2*m))
      = E213.Math.Real213.CutSum.cutSumAux
                (constCut 1 1) (constCut 1 1) k (2*(2*m)) (2*(2*m)) :=
    E213.Math.Real213.CutSumDetermined.cutSumAux_congr k (2*(2*m))
      (sf.derivative (constCut 1 2)) (constCut 1 1)
      (sg.derivative (constCut 1 2)) (constCut 1 1)
      (fun m' _ => hf m' (2*k))
      (fun m' _ => hg m' (2*k))
      (2*(2*m)) (Nat.le_refl _)
  rw [step]
  show cutMid (constCut 1 1) (constCut 1 1) m k = constCut 1 1 m k
  exact cutMid_self_constCut_at 1 1 m k (Nat.le_refl _)

/-- ★ Phase CK capstone (PURE) — generic propagation pointwise. -/
theorem propagation_capstone_pure :
    (∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative (constCut 1 2) m k = constCut 1 1 m k)
    ∧ (∀ m k, (midIsDifferentiable
                (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
                squareIsDifferentiable).derivative (constCut 1 2) m k
              = constCut 1 1 m k) :=
  ⟨mid_witness_propagates_at idIsDifferentiable squareIsDifferentiable
     (fun _ _ => rfl) squareDerivative_at_half_at,
   mid_witness_propagates_at
     (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
     squareIsDifferentiable
     mid_id_square_derivative_at_half_at
     squareDerivative_at_half_at⟩

end E213.Math.Real213.FluxMVTPropagate
