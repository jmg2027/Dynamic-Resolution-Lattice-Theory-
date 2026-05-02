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
open E213.Math.Real213.FluxMVTWitness (squareDerivative_at_half)
open E213.Math.Real213.FluxMVTMore (mid_id_square_derivative_at_half)
open E213.Math.Real213.CutMidSelf (cutMid_self_constCut)

/-- ★ Generic mid witness propagation at c = 1/2. -/
theorem mid_witness_propagates {f g}
    (sf : IsDifferentiable f) (sg : IsDifferentiable g)
    (hf : sf.derivative (constCut 1 2) = constCut 1 1)
    (hg : sg.derivative (constCut 1 2) = constCut 1 1) :
    (midIsDifferentiable sf sg).derivative (constCut 1 2)
      = constCut 1 1 := by
  show cutMid (sf.derivative (constCut 1 2))
              (sg.derivative (constCut 1 2)) = constCut 1 1
  rw [hf, hg]
  exact cutMid_self_constCut 1 1 (by decide)

/-- ★ Phase CK capstone: derive previous results via generic propagation. -/
theorem propagation_capstone :
    -- (1) Generic propagation
    (∀ {f g} (sf : IsDifferentiable f) (sg : IsDifferentiable g),
      sf.derivative (constCut 1 2) = constCut 1 1 →
      sg.derivative (constCut 1 2) = constCut 1 1 →
      (midIsDifferentiable sf sg).derivative (constCut 1 2) = constCut 1 1)
    -- (2) Specific: mid(x, x²) — derived via propagation
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1
    -- (3) Specific: mid(mid(x, x²), x²) — derived via propagation
    ∧ (midIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
        squareIsDifferentiable).derivative (constCut 1 2)
        = constCut 1 1 :=
  ⟨@mid_witness_propagates,
   mid_witness_propagates idIsDifferentiable squareIsDifferentiable
     rfl squareDerivative_at_half,
   mid_witness_propagates
     (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
     squareIsDifferentiable
     mid_id_square_derivative_at_half
     squareDerivative_at_half⟩

end E213.Math.Real213.FluxMVTPropagate
