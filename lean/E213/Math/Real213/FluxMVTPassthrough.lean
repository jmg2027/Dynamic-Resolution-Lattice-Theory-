import E213.Math.Real213.FluxMVTGeneric

/-!
# Research.Real213FluxMVTPassthrough

Phase BF: ★★ **General passthrough MVT theorem** ★★

ANY function f satisfying f(0) = 0 and f(1) = 1 has average rate
exactly 1 over [0, 1].  This is the dyadic native form of MVT
applied to any 1-cochain whose endpoints match the bracket endpoints.

  mvt_passthrough_unit          : f(0)=0, f(1)=1 → LD f unit = ofCut 1
  fluxAlong_passthrough_unit    : f(0)=0, f(1)=1 → flux f unit = ofCut 1
  ftc_bridge_passthrough_unit   : passthrough → LD = fluxAlong (FTC)

Generalizes Phase BE: not tied to polynomials.  Works for any
hypothetical function passing through both bracket endpoints —
including sin(πx/2), tanh, or any custom dyadic function.
-/

namespace E213.Math.Real213.FluxMVTPassthrough

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one_at cutMul_one_const_at)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero_at)

namespace FluxCut

/-- ★ Generic MVT for passthrough at unit bracket — forward field
    pointwise (∅-axiom). -/
theorem mvt_passthrough_unit_forward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_right : f (constCut 1 1) = constCut 1 1) (m k : Nat) :
    (localDivergence f unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (f (constCut 1 1)) m k = constCut 1 1 m k
  rw [h_right]
  exact cutMul_one_one_at m k

/-- ★ Generic MVT for passthrough at unit bracket — backward field
    pointwise (∅-axiom). -/
theorem mvt_passthrough_unit_backward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1) (m k : Nat) :
    (localDivergence f unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (f (constCut 0 1)) m k = constCut 0 1 m k
  rw [h_left]
  exact cutMul_one_const_at 0 1 m k

/-- ★ fluxAlong for passthrough at unit — forward pointwise (∅-axiom). -/
theorem fluxAlong_passthrough_unit_forward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_right : f (constCut 1 1) = constCut 1 1) (m k : Nat) :
    (fluxAlong f unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show f (constCut 1 1) m k = constCut 1 1 m k
  rw [h_right]

/-- ★ fluxAlong for passthrough at unit — backward pointwise (∅-axiom). -/
theorem fluxAlong_passthrough_unit_backward_at
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1) (m k : Nat) :
    (fluxAlong f unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show f (constCut 0 1) m k = constCut 0 1 m k
  rw [h_left]

/-! ### Pointwise / fluxCutEq variants — strict ∅-axiom (PURE)

These are the 213-native versions of the MVT/FTC bridge theorems
above.  They take pointwise hypotheses (`∀ m k, f (...) m k = ...`)
and produce `fluxCutEq` conclusions.  No funext in the chain. -/

open E213.Math.Real213.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)
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

/-- ★ **Generic MVT for passthrough at unit bracket** (fluxCutEq, PURE). -/
theorem mvt_passthrough_unit_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (mvt_passthrough_unit_forward_at_pure f h_right)
    (mvt_passthrough_unit_backward_at_pure f h_left)

/-- ★ **fluxAlong for passthrough functions at unit bracket** (fluxCutEq, PURE). -/
theorem fluxAlong_passthrough_unit_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (fluxAlong f unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise h_right h_left

/-- ★ **FTC bridge for passthrough** (fluxCutEq, PURE). -/
theorem ftc_bridge_passthrough_unit_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_trans
    (mvt_passthrough_unit_pure f h_left h_right)
    (E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_symm _ _
      (fluxAlong_passthrough_unit_pure f h_left h_right))

/-- Phase BF capstone (fluxCutEq, PURE) — passthrough MVT/FTC. -/
theorem phaseBF_capstone_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong f unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  ⟨mvt_passthrough_unit_pure f h_left h_right,
   fluxAlong_passthrough_unit_pure f h_left h_right,
   ftc_bridge_passthrough_unit_pure f h_left h_right⟩

end FluxCut

end E213.Math.Real213.FluxMVTPassthrough
