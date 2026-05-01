import E213.Math.Real213.FTCRiemannGeneric
import E213.Math.Real213.MVTWitnessChain

/-!
# Research.Real213FTCRiemannChain

Phase CD: applying generic FTC-Riemann to chain-rule constructions.

For id ∘ x² (= x² as function, but built via composeIsDifferentiable):
witness c = 1/2, passthrough endpoints, hence FTC-Riemann at depth 0
follows automatically from the generic theorem.
-/

namespace E213.Math.Real213.FTCRiemannChain

open E213.Firmware E213.Hypervisor

/-- ★ FTC-Riemann for id ∘ x² at unit depth 0 (via generic theorem). -/
theorem ftc_riemann_generic_for_id_compose_square :
    riemannSampleSum
        (composeIsDifferentiable squareIsDifferentiable
            idIsDifferentiable).derivative unitBracket 0
      = (FluxCut.fluxAlong ((fun x => x) ∘ (fun x => cutMul x x))
          unitBracket).forward :=
  ftc_riemann_generic_via_witness
    ((fun x => x) ∘ (fun x => cutMul x x))
    (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable)
    HasDyadicMVTWitness.id_compose_square rfl
    (by show cutMul (constCut 1 1) (constCut 1 1) = constCut 1 1
        exact cutMul_one_one)

/-- ★ FTC-Riemann for mid(x, x²) at unit depth 0 (via generic theorem). -/
theorem ftc_riemann_generic_for_mid :
    riemannSampleSum
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
            ).derivative unitBracket 0
      = (FluxCut.fluxAlong (fun x => cutMid x (cutMul x x))
          unitBracket).forward :=
  ftc_riemann_generic_via_witness
    (fun x => cutMid x (cutMul x x))
    (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
    HasDyadicMVTWitness.mid_id_square rfl
    (by show cutMid (constCut 1 1) (cutMul (constCut 1 1) (constCut 1 1))
            = constCut 1 1
        rw [cutMul_one_one]
        exact cutMid_self_constCut 1 1 (by decide))

/-- Phase CD capstone: 3-instance generic FTC-Riemann application. -/
theorem ftc_riemann_chain_capstone :
    riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
        = (FluxCut.fluxAlong (fun x => cutMul x x) unitBracket).forward
    ∧ riemannSampleSum
        (composeIsDifferentiable squareIsDifferentiable
            idIsDifferentiable).derivative unitBracket 0
        = (FluxCut.fluxAlong ((fun x => x) ∘ (fun x => cutMul x x))
            unitBracket).forward
    ∧ riemannSampleSum
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
            ).derivative unitBracket 0
        = (FluxCut.fluxAlong (fun x => cutMid x (cutMul x x))
            unitBracket).forward :=
  ⟨ftc_riemann_generic_for_square,
   ftc_riemann_generic_for_id_compose_square,
   ftc_riemann_generic_for_mid⟩

end E213.Math.Real213.FTCRiemannChain
