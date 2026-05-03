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
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.FluxCut (FluxCut)
open E213.Math.Real213.FluxCut.FluxCut (ofCut)
open E213.Math.Real213.DyadicBracket (DyadicBracket)
open E213.Math.Real213.FluxCochain.FluxCut (fluxAlong fluxAlong_id)
open E213.Math.Real213.FluxDivergence.FluxCut (localDivergence)
open E213.Math.Real213.DyadicTrajectory (unitBracket)
open E213.Math.Real213.CutMulOne (cutMul_one_one cutMul_one_const)
open E213.Math.Real213.CutSumZero (cutMul_zero_zero)

namespace FluxCut

/-- LD x⁴ at unit = ofCut 1. -/
theorem mvt_quartic_unitBracket :
    localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                    unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (constCut 1 1)
            (cutMul (cutMul (constCut 1 1) (constCut 1 1))
                    (cutMul (constCut 1 1) (constCut 1 1))),
          backward := cutMul (constCut 1 1)
            (cutMul (cutMul (constCut 0 1) (constCut 0 1))
                    (cutMul (constCut 0 1) (constCut 0 1))) } : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero, cutMul_one_one, cutMul_zero_zero,
      cutMul_one_one, cutMul_one_const 0 1]

/-- fluxAlong x⁴ at unit = ofCut 1. -/
theorem fluxAlong_quartic_unitBracket :
    fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x)) unitBracket
      = ofCut (constCut 1 1) := by
  show ({ forward := cutMul (cutMul (constCut 1 1) (constCut 1 1))
                            (cutMul (constCut 1 1) (constCut 1 1)),
          backward := cutMul (cutMul (constCut 0 1) (constCut 0 1))
                             (cutMul (constCut 0 1) (constCut 0 1)) }
                  : FluxCut)
       = { forward := constCut 1 1, backward := constCut 0 1 }
  rw [cutMul_one_one, cutMul_zero_zero, cutMul_one_one, cutMul_zero_zero]

/-- FTC bridge for x⁴: LD = fluxAlong. -/
theorem ftc_bridge_quartic_unitBracket :
    localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                    unitBracket
      = fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                  unitBracket := by
  rw [mvt_quartic_unitBracket, fluxAlong_quartic_unitBracket]

/-- Phase BD capstone: quartic MVT + FTC bridge at unit. -/
theorem phaseBD_capstone :
    localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                    unitBracket = ofCut (constCut 1 1)
    ∧ fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                      unitBracket
      = fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                  unitBracket :=
  ⟨mvt_quartic_unitBracket, fluxAlong_quartic_unitBracket,
   ftc_bridge_quartic_unitBracket⟩

/-! ### PURE pointwise variants (fluxCutEq form) — quartic via Pow 4

Note: x⁴ as `cutMul (cutMul x x) (cutMul x x)` is NOT definitionally
equal to `cutPow x 4`.  The pure form here would require either:
(a) restating via cutPow + cutPow_one_n_at, or
(b) inlining cutMulOuter_congr cascades.
Both are downstream from this file (need FluxMVTPassthrough or
additional cutMul congruence helpers).  Skipping — defer to next
session when the deeper FluxMVT stack is refactored. -/

end FluxCut

end E213.Math.Real213.FluxMVTHigh
