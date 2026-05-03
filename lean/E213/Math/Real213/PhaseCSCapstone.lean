import E213.Math.Real213.ClassicAnti

/-!
# Research.Real213PhaseCSCapstone

Phase CS: ★★ antiderivative arc unified capstone (CN-CR) ★★

Bundles every result on the IsAntiderivative class:
  CN: class definition + atomic instances
  CO: combinators (mid, add)
  CP: structural fromDifferentiable
  CQ: integral via antiderivative
  CR: ClassicCalc → IsAntiderivative connection
-/

namespace E213.Math.Real213.PhaseCSCapstone

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong)
open E213.Math.Real213.FluxFTCPolynomial.FluxCut
  (fluxAlong_square_unitBracket_forward_at
   fluxAlong_square_unitBracket_backward_at)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.IsDifferentiable
  (IsDifferentiable idIsDifferentiable constIsDifferentiable
   addIsDifferentiable)
open E213.Math.Real213.DifferentiableMid (midIsDifferentiable)
open E213.Math.Real213.Antiderivative (IsAntiderivative)
open E213.Math.Real213.Antiderivative.IsAntiderivative (id_anti)
open E213.Math.Real213.AntiderivativeStructural.IsAntiderivative
  (fromDifferentiable)
open E213.Math.Real213.IntegralViaAnti.IsAntiderivative
  (integral integral_one_unit)
open E213.Math.Real213.ClassicCalc (ClassicCalc ClassicCalc_at)
open E213.Math.Real213.ClassicCalc.ClassicCalc (id_calc square_calc)
open E213.Math.Real213.ClassicAnti.ClassicCalc
  (integralCC integralCC_id_unit integralCC_square_unit)
open E213.Math.Real213.ClassicAnti.ClassicCalc_at
  (integralCC_id_unit_forward_at integralCC_id_unit_backward_at
   integralCC_square_unit_forward_at integralCC_square_unit_backward_at
   integralCC_cube_unit_forward_at integralCC_cube_unit_backward_at)
open E213.Math.Real213.ClassicCalc.ClassicCalc_at
  renaming id_calc → id_calc_at, square_calc → square_calc_at, cube_calc → cube_calc_at

/-- ★★ **Phase CS antiderivative arc capstone**: 8-fact bundle ★★ -/
theorem phaseCS_antiderivative_capstone (db : DyadicBracket) :
    -- (CN) id antiderivative of constant 1
    idIsDifferentiable.derivative = constCutFn (constCut 1 1)
    -- (CN) constant antideriv of 0 (specific c = 0)
    ∧ (constIsDifferentiable (constCut 0 1)).derivative
        = constCutFn (constCut 0 1)
    -- (CO) mid combinator works
    ∧ (midIsDifferentiable idIsDifferentiable idIsDifferentiable).derivative
        = (fun x => cutMid (constCut 1 1) (constCut 1 1))
    -- (CO) add combinator works
    ∧ (addIsDifferentiable idIsDifferentiable idIsDifferentiable).derivative
        = (fun x => cutSum (constCut 1 1) (constCut 1 1))
    -- (CP) structural fromDifferentiable: id_calc gives IsAnti
    ∧ Nonempty (IsAntiderivative id idIsDifferentiable
                  idIsDifferentiable.derivative)
    -- (CQ) integral of 1 over unit = 1
    ∧ integral id_anti unitBracket = ofCut (constCut 1 1)
    -- (CR) ClassicCalc → IsAntiderivative
    ∧ integralCC id_calc unitBracket = ofCut (constCut 1 1)
    -- (CR) integralCC for square at unit
    ∧ integralCC square_calc unitBracket = ofCut (constCut 1 1) :=
  ⟨rfl, rfl, rfl, rfl,
   ⟨fromDifferentiable idIsDifferentiable⟩,
   integral_one_unit,
   integralCC_id_unit,
   integralCC_square_unit⟩

/-- ★★ **Phase CS pointwise PURE capstone** ★★

    Strict ∅-axiom version of the antiderivative arc capstone,
    extended via ClassicCalc_at to cover square and cube parts. -/
theorem phaseCS_antiderivative_capstone_at (m k : Nat) :
    -- (CN) id antiderivative of constant 1
    idIsDifferentiable.derivative (constCut 0 1) m k = constCut 1 1 m k
    -- (CQ) integral of 1 over unit forward = constCut 1 1
    ∧ (integral id_anti unitBracket).forward m k
        = (ofCut (constCut 1 1) : FluxCut).forward m k
    -- (CQ) integral of 1 over unit backward = constCut 0 1
    ∧ (integral id_anti unitBracket).backward m k
        = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (CR) integralCC id_calc_at at unit forward
    ∧ (E213.Math.Real213.ClassicAnti.ClassicCalc_at.integralCC
        id_calc_at unitBracket).forward m k
        = (ofCut (constCut 1 1) : FluxCut).forward m k
    -- (CR) integralCC id_calc_at at unit backward
    ∧ (E213.Math.Real213.ClassicAnti.ClassicCalc_at.integralCC
        id_calc_at unitBracket).backward m k
        = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (CR) integralCC square_calc_at at unit forward
    ∧ (E213.Math.Real213.ClassicAnti.ClassicCalc_at.integralCC
        square_calc_at unitBracket).forward m k
        = (ofCut (constCut 1 1) : FluxCut).forward m k
    -- (CR) integralCC square_calc_at at unit backward
    ∧ (E213.Math.Real213.ClassicAnti.ClassicCalc_at.integralCC
        square_calc_at unitBracket).backward m k
        = (ofCut (constCut 1 1) : FluxCut).backward m k
    -- (CR) integralCC cube_calc_at at unit forward
    ∧ (E213.Math.Real213.ClassicAnti.ClassicCalc_at.integralCC
        cube_calc_at unitBracket).forward m k
        = (ofCut (constCut 1 1) : FluxCut).forward m k
    -- (CR) integralCC cube_calc_at at unit backward
    ∧ (E213.Math.Real213.ClassicAnti.ClassicCalc_at.integralCC
        cube_calc_at unitBracket).backward m k
        = (ofCut (constCut 1 1) : FluxCut).backward m k :=
  ⟨rfl, rfl, rfl,
   integralCC_id_unit_forward_at m k,
   integralCC_id_unit_backward_at m k,
   integralCC_square_unit_forward_at m k,
   integralCC_square_unit_backward_at m k,
   integralCC_cube_unit_forward_at m k,
   integralCC_cube_unit_backward_at m k⟩

end E213.Math.Real213.PhaseCSCapstone
