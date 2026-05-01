import E213.Research.Real213.FluxMVTNested

/-!
# Research.Real213FluxMVTPattern

Phase CG: pattern observation — dyadic witness catalog summary.

All known constructive dyadic MVT witnesses share c = 1/2:

  Function                                  Witness
  ─────────────────────────────────────    ─────────
  id (linear)                               any c
  x²                                        1/2
  mid(x, x²)                                1/2
  id ∘ x²                                   1/2
  mid(x, mid(x, x²))                        1/2

Pattern: any function buildable via { id, x², mid, id-compose }
combinators has dyadic MVT witness c = 1/2.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- ★ Phase CG capstone: 5-instance dyadic witness catalog at c = 1/2. -/
theorem dyadic_witness_pattern_capstone :
    -- (1) id at c = 1/2
    idIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    -- (2) x² at c = 1/2
    ∧ squareIsDifferentiable.derivative (constCut 1 2) = constCut 1 1
    -- (3) mid(x, x²) at c = 1/2
    ∧ (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1
    -- (4) id ∘ x² at c = 1/2
    ∧ (composeIsDifferentiable squareIsDifferentiable idIsDifferentiable
        ).derivative (constCut 1 2) = constCut 1 1
    -- (5) mid(x, mid(x, x²)) at c = 1/2
    ∧ (midIsDifferentiable idIsDifferentiable
        (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
            ).derivative (constCut 1 2) = constCut 1 1 :=
  ⟨rfl, squareDerivative_at_half, mid_id_square_derivative_at_half,
   id_compose_square_derivative_at_half,
   mid_id_mid_id_square_derivative_at_half⟩

/-- ★ Existential MVT for all 5 functions (constructive). -/
theorem dyadic_witness_existential_capstone :
    (∃ c, idIsDifferentiable.derivative c = constCut 1 1)
    ∧ (∃ c, squareIsDifferentiable.derivative c = constCut 1 1)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative c = constCut 1 1)
    ∧ (∃ c, (composeIsDifferentiable squareIsDifferentiable
              idIsDifferentiable).derivative c = constCut 1 1)
    ∧ (∃ c, (midIsDifferentiable idIsDifferentiable
              (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
                )).derivative c = constCut 1 1) :=
  ⟨⟨constCut 0 1, rfl⟩,
   square_has_dyadic_witness,
   ⟨constCut 1 2, mid_id_square_derivative_at_half⟩,
   id_compose_square_has_dyadic_witness,
   mid_id_mid_id_square_has_dyadic_witness⟩

end E213.Research.Real213.CutSum
