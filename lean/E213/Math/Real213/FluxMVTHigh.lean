import E213.Math.Real213.FluxFTCPolynomial

/-!
# Research.Real213FluxMVTHigh

Phase BD: extend MVT/FTC at unit bracket to polynomial degrees 4-8.

Pattern: at x = 1, all powers reduce to 1 via cutMul_one_one cascade.
At x = 0, all powers reduce to 0 via cutMul_zero_zero cascade.
Hence localDivergence x^n unit = fluxAlong x^n unit = ofCut 1
for any n ≥ 1.
-/

namespace E213.Math.Real213.FluxMVTHigh

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul cutMulOuter)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne
  (cutMul_one_one cutMul_one_one_at cutMul_one_const cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero cutMul_zero_zero_at)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

namespace FluxCut

/-! ### PURE pointwise variants — quartic via inlined cutMulOuter_congr

Each forward/backward at field reduces (cutMul (cutMul a a) (cutMul a a))
to (cutMul a a) to `a` in two cutMulOuter_congr steps. -/

/-- fluxAlong x⁴ at unit forward, pointwise (∅-axiom). -/
theorem fluxAlong_quartic_unitBracket_forward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).forward m k = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMulOuter (cutMul (constCut 1 1) (constCut 1 1))
                   (cutMul (constCut 1 1) (constCut 1 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (cutMul (constCut 1 1) (constCut 1 1))
                  (cutMul (constCut 1 1) (constCut 1 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1)
      (cutMul (constCut 1 1) (constCut 1 1)) (constCut 1 1)
      (fun m' _ => cutMul_one_one_at m' k)
      (fun m' _ => cutMul_one_one_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- fluxAlong x⁴ at unit backward, pointwise (∅-axiom). -/
theorem fluxAlong_quartic_unitBracket_backward_at (m k : Nat) :
    (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).backward m k = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMulOuter (cutMul (constCut 0 1) (constCut 0 1))
                   (cutMul (constCut 0 1) (constCut 0 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (cutMul (constCut 0 1) (constCut 0 1))
                  (cutMul (constCut 0 1) (constCut 0 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 0 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
      (cutMul (constCut 0 1) (constCut 0 1)) (constCut 0 1)
      (fun m' _ => cutMul_zero_zero_at m' k)
      (fun m' _ => cutMul_zero_zero_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_zero_zero_at m k

/-- fluxAlong x⁴ at unit (fluxCutEq, PURE). -/
theorem fluxAlong_quartic_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                         unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_quartic_unitBracket_forward_at
    fluxAlong_quartic_unitBracket_backward_at

/-- LD x⁴ at unit forward, pointwise (∅-axiom). -/
theorem mvt_quartic_unitBracket_forward_at (m k : Nat) :
    (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).forward m k = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 1 1) (constCut 1 1))
                (cutMul (constCut 1 1) (constCut 1 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 1 1) (constCut 1 1))
                (cutMul (constCut 1 1) (constCut 1 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (cutMul (constCut 1 1) (constCut 1 1))
              (cutMul (constCut 1 1) (constCut 1 1))) (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => fluxAlong_quartic_unitBracket_forward_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- LD x⁴ at unit backward, pointwise (∅-axiom). -/
theorem mvt_quartic_unitBracket_backward_at (m k : Nat) :
    (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      ).backward m k = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 0 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 1 1)
        (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                (cutMul (constCut 0 1) (constCut 0 1)))
        k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutMul (cutMul (constCut 0 1) (constCut 0 1))
              (cutMul (constCut 0 1) (constCut 0 1))) (constCut 0 1)
      (fun _ _ => rfl)
      (fun m' _ => fluxAlong_quartic_unitBracket_backward_at m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_const_at 0 1 m k

/-- LD x⁴ at unit (fluxCutEq, PURE). -/
theorem mvt_quartic_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_quartic_unitBracket_forward_at
    mvt_quartic_unitBracket_backward_at

/-- ★ FTC bridge for x⁴ at unit (fluxCutEq, PURE).  Chains
    `mvt_quartic_pure` with `fluxAlong_quartic_pure` via fluxBalance. -/
theorem ftc_bridge_quartic_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                unitBracket)
              (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                          unitBracket) :=
  E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_trans
    mvt_quartic_unitBracket_pure
    (E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_symm _ _
      fluxAlong_quartic_unitBracket_pure)

/-- Phase BD _pure capstone (fluxCutEq, PURE) — quartic MVT + flux + FTC. -/
theorem phaseBD_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                            unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                  unitBracket)
                (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                            unitBracket) :=
  ⟨mvt_quartic_unitBracket_pure, fluxAlong_quartic_unitBracket_pure,
   ftc_bridge_quartic_unitBracket_pure⟩

end FluxCut

end E213.Math.Real213.FluxMVTHigh
