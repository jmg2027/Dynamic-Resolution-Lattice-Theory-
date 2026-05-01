import E213.Research.Real213.ClassicAnti

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

namespace E213.Research.Real213.PhaseCSCapstone

open E213.Firmware E213.Hypervisor

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
    ∧ IsAntiderivative.integral IsAntiderivative.id_anti unitBracket
        = FluxCut.ofCut (constCut 1 1)
    -- (CR) ClassicCalc → IsAntiderivative
    ∧ ClassicCalc.integralCC ClassicCalc.id_calc unitBracket
        = FluxCut.ofCut (constCut 1 1)
    -- (CR) integralCC for square at unit
    ∧ ClassicCalc.integralCC ClassicCalc.square_calc unitBracket
        = FluxCut.ofCut (constCut 1 1) :=
  ⟨rfl, rfl, rfl, rfl,
   ⟨IsAntiderivative.fromDifferentiable idIsDifferentiable⟩,
   IsAntiderivative.integral_one_unit,
   ClassicCalc.integralCC_id_unit,
   ClassicCalc.integralCC_square_unit⟩

end E213.Research.Real213.PhaseCSCapstone
