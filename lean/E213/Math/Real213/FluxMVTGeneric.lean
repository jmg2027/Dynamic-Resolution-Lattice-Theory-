import E213.Math.Real213.FluxMVTHigh
import E213.Math.Real213.CutPowConst
import E213.Math.Real213.CutMulDetermined

/-!
# Research.Real213FluxMVTGeneric

Phase BE: ★ **Generic MVT/FTC at unit bracket for cutPow x^(n+1)** ★

For any n ≥ 1, MVT and FTC hold *propositionally* at unit bracket.
Single 1-line proofs leveraging cutPow_one_n + cutPow_zero_succ.

This is the *quantified* form: ∀ n, the framework gives MVT/FTC.
No induction needed at the framework layer — the cut-level lemmas
already do all the work.
-/

namespace E213.Math.Real213.FluxMVTGeneric

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutPowConst
  (cutPow_one_const cutPow_one_n cutPow_one_n_at
   cutPow_zero_succ cutPow_zero_succ_at)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulOne
  (cutMul_one_one cutMul_one_one_at cutMul_one_const cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)

namespace FluxCut

/-- ★ Generic MVT for x^(n+1) at unit — forward field pointwise (∅-axiom). -/
theorem mvt_cutPow_unitBracket_forward_at (n m k : Nat) :
    (localDivergence (fun x => cutPow x (n+1)) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (cutPow (constCut 1 1) (n+1)) m k
       = constCut 1 1 m k
  show cutMulOuter (constCut 1 1) (cutPow (constCut 1 1) (n+1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutPow (constCut 1 1) (n+1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutPow (constCut 1 1) (n+1)) (constCut 1 1)
      (fun _ _ => rfl)
      (fun m' _ => cutPow_one_n_at (n+1) m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

/-- ★ Generic MVT for x^(n+1) at unit — backward pointwise (∅-axiom). -/
theorem mvt_cutPow_unitBracket_backward_at (n m k : Nat) :
    (localDivergence (fun x => cutPow x (n+1)) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (cutPow (constCut 0 1) (n+1)) m k
       = constCut 0 1 m k
  show cutMulOuter (constCut 1 1) (cutPow (constCut 0 1) (n+1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (constCut 1 1) (cutPow (constCut 0 1) (n+1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1)
      (cutPow (constCut 0 1) (n+1)) (constCut 0 1)
      (fun _ _ => rfl)
      (fun m' _ => cutPow_zero_succ_at n m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_const_at 0 1 m k


/-! ### PURE pointwise variants (fluxCutEq form)

Uses local `_at` field theorems + `fluxCutEq_of_pointwise` (PURE).
No funext, no propext.  Cannot use FluxMVTPassthrough _pure
forms — they live downstream. -/

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)

/-- fluxAlong x^(n+1) at unit forward, pointwise (∅-axiom). -/
theorem fluxAlong_cutPow_unitBracket_forward_at (n m k : Nat) :
    (fluxAlong (fun x => cutPow x (n+1)) unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k :=
  cutPow_one_n_at (n+1) m k

/-- fluxAlong x^(n+1) at unit backward, pointwise (∅-axiom). -/
theorem fluxAlong_cutPow_unitBracket_backward_at (n m k : Nat) :
    (fluxAlong (fun x => cutPow x (n+1)) unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k :=
  cutPow_zero_succ_at n m k

/-- ★ Generic MVT for x^(n+1) at unit (fluxCutEq, PURE). -/
theorem mvt_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (mvt_cutPow_unitBracket_forward_at n)
    (mvt_cutPow_unitBracket_backward_at n)

/-- ★ Generic fluxAlong for x^(n+1) at unit (fluxCutEq, PURE). -/
theorem fluxAlong_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (fluxAlong_cutPow_unitBracket_forward_at n)
    (fluxAlong_cutPow_unitBracket_backward_at n)

/-- ★ Generic FTC bridge for x^(n+1) at unit (fluxCutEq, PURE). -/
theorem ftc_bridge_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (fluxAlong (fun x => cutPow x (n+1)) unitBracket) :=
  E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_trans
    (mvt_cutPow_unitBracket_pure n)
    (E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_symm _ _
      (fluxAlong_cutPow_unitBracket_pure n))

/-- Phase BE capstone (fluxCutEq, PURE) — MVT + fluxAlong + FTC bridge. -/
theorem phaseBE_capstone_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
                (fluxAlong (fun x => cutPow x (n+1)) unitBracket) :=
  ⟨mvt_cutPow_unitBracket_pure n, fluxAlong_cutPow_unitBracket_pure n,
   ftc_bridge_cutPow_unitBracket_pure n⟩

end FluxCut

end E213.Math.Real213.FluxMVTGeneric
