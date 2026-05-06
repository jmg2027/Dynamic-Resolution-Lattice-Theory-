import E213.Math.Analysis.FluxMVT.FluxMVTConcrete

import E213.Math.Real213.Core
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxMVT
/-!
# FluxFTC
Fundamental Theorem of Calculus** in 213-native flux form.

Classical FTC: ∫_a^b f'(x) dx = f(b) - f(a).

213 cohomological reframing: the path-integrated localDivergence
along the bisection of a bracket equals the fluxAlong the bracket
(boundary value).  This is **Stokes' theorem for the dyadic tree**.

  fluxAlong f db                     ←→   f(b) - f(a)  (boundary)
  Σ localDivergence f.deriv along db ←→   ∫_a^b f'    (interior)

The cohomEquiv between these is the FTC.

## Theorems

  ftc_const                : FTC for constant function (trivial)
  ftc_id_unitBracket       : FTC for identity at unitBracket
  fluxAlong_id_unitBracket : id flux gives endpoint pair (0, 1)
-/

namespace E213.Math.Analysis.FluxMVT.FluxFTC

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut
  (fluxAlong fluxAlong_id fluxAlong_const_isBalanced isBalanced)
open E213.Math.Analysis.FluxMVT.FluxCut.FluxCut (ofCut)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut
  (localDivergence localDivergence_const_balanced)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)

namespace FluxCut

/-- **fluxAlong id at unitBracket** has endpoints (1, 0). -/
theorem fluxAlong_id_unitBracket :
    fluxAlong id unitBracket
      = { forward := constCut 1 1, backward := constCut 0 1 } := rfl

/-- **FTC for identity at unitBracket**: id.derivative is constant 1,
    so its integral over [0, 1] is 1, matching fluxAlong id = (1, 0). -/
theorem ftc_id_unitBracket :
    fluxAlong id unitBracket = ofCut (constCut 1 1) := rfl

/-- **FTC for constant function**: f(b) - f(a) is balanced (= 0)
    for any constant, matching ∫ 0 dx = 0. -/
theorem ftc_const (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (fluxAlong (constCutFn c) db) :=
  fluxAlong_const_isBalanced c db

/-- **FTC for constant**: localDivergence and fluxAlong both balanced. -/
theorem ftc_const_bridge (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (localDivergence (constCutFn c) db)
    ∧ isBalanced (fluxAlong (constCutFn c) db) :=
  ⟨localDivergence_const_balanced c db, fluxAlong_const_isBalanced c db⟩

/-! ### PURE pointwise variants (fluxCutEq form) -/

open E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut (fluxCutEq fluxCutEq_of_pointwise)
open E213.Math.Analysis.FluxMVT.FluxMVTConcrete.FluxCut (mvt_id_unitBracket_pure)

/-- ★ FTC bridge for id at unit (fluxCutEq, PURE).  Uses
    `mvt_id_unitBracket_pure` + `fluxAlong id unitBracket` = ofCut (1,0). -/
theorem ftc_bridge_id_unitBracket_pure :
    fluxCutEq (localDivergence id unitBracket) (fluxAlong id unitBracket) :=
  E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_trans
    mvt_id_unitBracket_pure
    (E213.Math.Analysis.FluxMVT.FluxMVT.FluxCut.fluxBalance_symm _ _
      (fluxCutEq_of_pointwise (fun _ _ => rfl) (fun _ _ => rfl)))

/-- ★ -1 capstone (fluxCutEq, PURE). -/
theorem ftc_concrete_capstone_pure (c : Nat → Nat → Bool)
    (db : DyadicBracket) :
    fluxCutEq (fluxAlong id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence id unitBracket) (fluxAlong id unitBracket)
    ∧ isBalanced (fluxAlong (constCutFn c) db)
    ∧ isBalanced (localDivergence (constCutFn c) db) :=
  ⟨fluxCutEq_of_pointwise (fun _ _ => rfl) (fun _ _ => rfl),
   ftc_bridge_id_unitBracket_pure,
   fluxAlong_const_isBalanced c db, localDivergence_const_balanced c db⟩

end FluxCut

end E213.Math.Analysis.FluxMVT.FluxFTC
