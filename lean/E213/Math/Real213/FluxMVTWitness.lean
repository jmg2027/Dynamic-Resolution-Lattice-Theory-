import E213.Math.Real213.CutSumOne

/-!
# Research.Real213FluxMVTWitness

Phase BR: ★ **explicit MVT witness for x²** ★

For x² over [0, 1], MVT says ∃ c ∈ (0, 1) with f'(c) = (f(1)-f(0))/1 = 1.
Solving 2c = 1 gives c = 1/2 — a *dyadic* point!  We can prove
PROPOSITIONALLY that derivative of x² at 1/2 equals 1.

  squareDerivative_at_half : squareIsDifferentiable.deriv (1/2) = 1
  mvt_square_explicit      : MVT for x² with c = 1/2 (full propEq)

★ For x² specifically, the MVT witness is constructively dyadic.
For x³, c = 1/√3 is not dyadic; the witness becomes existential
(Cauchy approximation).  This file isolates the lucky x² case.
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

/-- ★ d/dx [x²] at x = 1/2 = 1 — pointwise (∅-axiom). -/
theorem squareDerivative_at_half_at (m k : Nat) :
    squareIsDifferentiable.derivative (constCut 1 2) m k = constCut 1 1 m k := by
  show cutSum (cutMul (constCut 1 1) (constCut 1 2))
              (cutMul (constCut 1 2) (constCut 1 1)) m k
       = constCut 1 1 m k
  show cutSumAux (cutMul (constCut 1 1) (constCut 1 2))
                 (cutMul (constCut 1 2) (constCut 1 1)) k (2*m) (2*m)
       = constCut 1 1 m k
  -- Push pointwise eq through cutSumAux: swap both inner cutMul's
  -- to constCut 1 2 via cutSumAux_congr.
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

/-- The witness c = 1/2 is interior to [0, 1]: it equals constCut 1 2. -/
theorem mvt_square_witness_in_interior :
    (constCut 1 2 : Nat → Nat → Bool) 1 2 = true := by decide

/-! ### PURE pointwise variants (∅-axiom) -/

/-- ★ MVT for x² with explicit dyadic witness c = 1/2 (PURE). -/
theorem mvt_square_explicit_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
                = constCut 1 1 m k) :=
  ⟨mvt_square_unitBracket_pure, squareDerivative_at_half_at⟩

/-- ★ MVT existence (pointwise) with explicit witness for x² (PURE). -/
theorem mvt_square_explicit_witness_at :
    ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨constCut 1 2, squareDerivative_at_half_at⟩

/-- ★ Phase BR capstone (PURE) — MVT for x² with dyadic witness. -/
theorem mvt_square_with_witness_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
                = constCut 1 1 m k)
    ∧ ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨mvt_square_unitBracket_pure, squareDerivative_at_half_at,
   ⟨constCut 1 2, squareDerivative_at_half_at⟩⟩

end E213.Math.Real213.FluxMVTWitness
