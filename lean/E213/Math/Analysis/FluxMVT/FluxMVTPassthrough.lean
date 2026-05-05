import E213.Math.Analysis.FluxMVT.FluxMVTPolynomial

import E213.Math.Real213.Core
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutMulDetermined
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutPowConst
import E213.Math.Real213.CutSumTest
import E213.Math.Real213.CutSumZero
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxMVT
/-!
# Passthrough MVT theorem + closure + applications

**Passthrough principle**: any function `f` satisfying `f(0) = 0` and
`f(1) = 1` has average rate exactly `1` over `[0, 1]`.  This is the
dyadic-native form of the MVT applied to any 1-cochain whose endpoints
match the bracket endpoints.

The principle is closed under composition / midpoint / multiplication
of passthrough functions, so `id`, `x²`, `x³`, `x^(n+1)`, and arbitrary
combinator-built functions all inherit MVT/FTC at unit bracket as
direct corollaries.

Sub-namespaces preserved (cross-file `open` declarations stay valid):

  * `E213.Math.Analysis.FluxMVT.FluxMVTPassthrough`   — the general theorem
  * `E213.Math.Analysis.FluxMVTClosure`       — closure under combinators
  * `E213.Math.Analysis.FluxMVTApplications`  — corollaries for id / cutPow / x² / x³

(Consolidated 2026-05-05 from 3 FluxMVTPassthrough
[] + FluxMVTClosure [] + FluxMVTApplications [].
Per-stage capstones dropped.)
-/

namespace E213.Math.Analysis.FluxMVT.FluxMVTPassthrough

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)

namespace FluxCut

/-- Generic MVT for passthrough at unit — forward field (pointwise ∅-axiom). -/
theorem mvt_passthrough_unit_forward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_right : f (constCut 1 1) = constCut 1 1) (m k : Nat) :
    (localDivergence f unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (f (constCut 1 1)) m k = constCut 1 1 m k
  rw [h_right]
  exact cutMul_one_one_at m k

/-- Generic MVT for passthrough at unit — backward field (pointwise ∅-axiom). -/
theorem mvt_passthrough_unit_backward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1) (m k : Nat) :
    (localDivergence f unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (f (constCut 0 1)) m k = constCut 0 1 m k
  rw [h_left]
  exact cutMul_one_const_at 0 1 m k

/-- fluxAlong for passthrough at unit — forward (pointwise ∅-axiom). -/
theorem fluxAlong_passthrough_unit_forward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_right : f (constCut 1 1) = constCut 1 1) (m k : Nat) :
    (fluxAlong f unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show f (constCut 1 1) m k = constCut 1 1 m k
  rw [h_right]

/-- fluxAlong for passthrough at unit — backward (pointwise ∅-axiom). -/
theorem fluxAlong_passthrough_unit_backward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1) (m k : Nat) :
    (fluxAlong f unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show f (constCut 0 1) m k = constCut 0 1 m k
  rw [h_left]

/-! ### PURE pointwise variants (fluxCutEq form) — strict ∅-axiom -/

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.CutMul (cutMulOuter)

/-- Forward field — fully pointwise (PURE). -/
theorem mvt_passthrough_unit_forward_at_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) (m k : Nat) :
    (localDivergence f unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (f (constCut 1 1)) m k = constCut 1 1 m k
  show cutMulOuter (constCut 1 1) (f (constCut 1 1)) k m
         ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step : cutMulOuter (constCut 1 1) (f (constCut 1 1)) k m
                  ((m+1)*(k+1)) ((m+1)*(k+1))
            = cutMulOuter (constCut 1 1) (constCut 1 1) k m
                  ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1) (f (constCut 1 1)) (constCut 1 1)
      (fun _ _ => rfl) (fun m' _ => h_right m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_one_at m k

/-- Backward field — fully pointwise (PURE). -/
theorem mvt_passthrough_unit_backward_at_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k) (m k : Nat) :
    (localDivergence f unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (f (constCut 0 1)) m k = constCut 0 1 m k
  show cutMulOuter (constCut 1 1) (f (constCut 0 1)) k m
         ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step : cutMulOuter (constCut 1 1) (f (constCut 0 1)) k m
                  ((m+1)*(k+1)) ((m+1)*(k+1))
            = cutMulOuter (constCut 1 1) (constCut 0 1) k m
                  ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (constCut 1 1) (constCut 1 1) (f (constCut 0 1)) (constCut 0 1)
      (fun _ _ => rfl) (fun m' _ => h_left m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]
  exact cutMul_one_const_at 0 1 m k

/-- Generic MVT for passthrough at unit (fluxCutEq, PURE). -/
theorem mvt_passthrough_unit_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (mvt_passthrough_unit_forward_at_pure f h_right)
    (mvt_passthrough_unit_backward_at_pure f h_left)

/-- fluxAlong for passthrough at unit (fluxCutEq, PURE). -/
theorem fluxAlong_passthrough_unit_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (fluxAlong f unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise h_right h_left

/-- FTC bridge for passthrough (fluxCutEq, PURE). -/
theorem ftc_bridge_passthrough_unit_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_trans
    (mvt_passthrough_unit_pure f h_left h_right)
    (E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_symm _ _
      (fluxAlong_passthrough_unit_pure f h_left h_right))

end FluxCut

end E213.Math.Analysis.FluxMVT.FluxMVTPassthrough

namespace E213.Math.Analysis.FluxMVTClosure

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)

namespace FluxCut

/-- Passthrough is closed under composition. -/
theorem passthrough_compose
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : f (constCut 0 1) = constCut 0 1)
    (hf_right : f (constCut 1 1) = constCut 1 1)
    (hg_left : g (constCut 0 1) = constCut 0 1)
    (hg_right : g (constCut 1 1) = constCut 1 1) :
    (g ∘ f) (constCut 0 1) = constCut 0 1
    ∧ (g ∘ f) (constCut 1 1) = constCut 1 1 := by
  refine ⟨?_, ?_⟩
  · show g (f (constCut 0 1)) = constCut 0 1
    rw [hf_left, hg_left]
  · show g (f (constCut 1 1)) = constCut 1 1
    rw [hf_right, hg_right]

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Analysis.FluxMVT.FluxMVTPassthrough.FluxCut
  (mvt_passthrough_unit_pure)
open E213.Math.Real213.CutMul (cutMulOuter)
open E213.Math.Real213.CutMulDetermined (cutMulOuter_congr)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)

/-- Passthrough closed under cutMul — left, fully pointwise (∅-axiom). -/
theorem passthrough_mul_at_left
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (hg_left : ∀ m k, g (constCut 0 1) m k = constCut 0 1 m k)
    (m k : Nat) :
    cutMul (f (constCut 0 1)) (g (constCut 0 1)) m k = constCut 0 1 m k := by
  show cutMulOuter (f (constCut 0 1)) (g (constCut 0 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step :
      cutMulOuter (f (constCut 0 1)) (g (constCut 0 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 0 1) (constCut 0 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (f (constCut 0 1)) (constCut 0 1)
      (g (constCut 0 1)) (constCut 0 1)
      (fun m' _ => hf_left m' k)
      (fun m' _ => hg_left m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_zero_zero_at m k

/-- Passthrough closed under cutMul — right, fully pointwise (∅-axiom). -/
theorem passthrough_mul_at_right
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k)
    (hg_right : ∀ m k, g (constCut 1 1) m k = constCut 1 1 m k)
    (m k : Nat) :
    cutMul (f (constCut 1 1)) (g (constCut 1 1)) m k = constCut 1 1 m k := by
  show cutMulOuter (f (constCut 1 1)) (g (constCut 1 1))
                   k m ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step :
      cutMulOuter (f (constCut 1 1)) (g (constCut 1 1))
                  k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut 1 1) (constCut 1 1)
                  k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
    cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
      (f (constCut 1 1)) (constCut 1 1)
      (g (constCut 1 1)) (constCut 1 1)
      (fun m' _ => hf_right m' k)
      (fun m' _ => hg_right m' k)
      ((m+1)*(k+1)) (Nat.le_refl _)
  rw [step]; exact cutMul_one_one_at m k

/-- MVT for product of passthroughs (fluxCutEq, PURE). -/
theorem mvt_mul_passthrough_pure
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (hf_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k)
    (hg_left : ∀ m k, g (constCut 0 1) m k = constCut 0 1 m k)
    (hg_right : ∀ m k, g (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence (fun x => cutMul (f x) (g x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutMul (f x) (g x))
    (passthrough_mul_at_left f g hf_left hg_left)
    (passthrough_mul_at_right f g hf_right hg_right)

end FluxCut

end E213.Math.Analysis.FluxMVTClosure

namespace E213.Math.Analysis.FluxMVTApplications

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPow (cutPow)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)

namespace FluxCut

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq)
open E213.Math.Analysis.FluxMVT.FluxMVTPassthrough.FluxCut (mvt_passthrough_unit_pure)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)
open E213.Math.Real213.CutPowConst (cutPow_one_n_at cutPow_zero_succ_at)

/-- id MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_id_via_passthrough_pure :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure id (fun _ _ => rfl) (fun _ _ => rfl)

/-- x^(n+1) MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_cutPow_via_passthrough_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutPow x (n+1))
    (cutPow_zero_succ_at n) (cutPow_one_n_at (n+1))

/-- x² MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_square_via_passthrough_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutMul x x)
    cutMul_zero_zero_at cutMul_one_one_at

/-- x³ MVT via passthrough (fluxCutEq, PURE). -/
theorem mvt_cube_via_passthrough_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutMul x (cutMul x x))
    (E213.Math.Analysis.FluxMVT.FluxMVTPolynomial.FluxCut.fluxAlong_cube_unitBracket_backward_at)
    (E213.Math.Analysis.FluxMVT.FluxMVTPolynomial.FluxCut.fluxAlong_cube_unitBracket_forward_at)

end FluxCut

end E213.Math.Analysis.FluxMVTApplications
