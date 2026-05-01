import E213.Research.Real213.FluxMVTGeneric

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

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

namespace FluxCut

/-- ★ **Generic MVT for passthrough functions at unit bracket** ★

    For any f with f(0) = 0 and f(1) = 1 (taking left/right endpoints
    to themselves), the average rate of f over [0, 1] is exactly 1. -/
theorem mvt_passthrough_unit
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) :
    localDivergence f unitBracket = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1) (f (constCut 1 1)),
          backward := cutMul (constCut 1 1) (f (constCut 0 1)) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [h_left, h_right, cutMul_one_one, cutMul_one_const 0 1]

/-- ★ **fluxAlong for passthrough functions at unit bracket** ★ -/
theorem fluxAlong_passthrough_unit
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) :
    fluxAlong f unitBracket = ofCut (constCut 1 1) := by
  show ({ forward := f (constCut 1 1),
          backward := f (constCut 0 1) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [h_left, h_right]

/-- ★ **FTC bridge for passthrough functions** ★ -/
theorem ftc_bridge_passthrough_unit
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) :
    localDivergence f unitBracket = fluxAlong f unitBracket := by
  rw [mvt_passthrough_unit f h_left h_right,
      fluxAlong_passthrough_unit f h_left h_right]

/-- Phase BF capstone: passthrough MVT/FTC. -/
theorem phaseBF_capstone (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) :
    localDivergence f unitBracket = ofCut (constCut 1 1)
    ∧ fluxAlong f unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence f unitBracket = fluxAlong f unitBracket :=
  ⟨mvt_passthrough_unit f h_left h_right,
   fluxAlong_passthrough_unit f h_left h_right,
   ftc_bridge_passthrough_unit f h_left h_right⟩

end FluxCut

end E213.Research.Real213.CutSum
