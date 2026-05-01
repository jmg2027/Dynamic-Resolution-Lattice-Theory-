import E213.Research.Real213.ClassicCalcExtreme

/-!
# Research.Real213ClassicCalcGeneric

Phase BP: ★ generic `ClassicCalc (fun x => cutPow x (n+1))` ★

Single instance covers ALL polynomial degrees x^(n+1) at once.
One-liner MVT/FTC for arbitrary n via `.mvt` and `.ftc`.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

namespace ClassicCalc

/-- ★ Generic polynomial chain ClassicCalc instance for any n. -/
def cutPow_calc (n : Nat) : ClassicCalc (fun x => cutPow x (n+1)) :=
  { diff := cutPowFnIsDifferentiable (n+1)
    pass := FluxCut.Passthrough.cutPow_pass n }

/-- ★ Generic MVT for x^(n+1) (∀ n) — one-liner via cutPow_calc. -/
theorem cutPow_calc_mvt (n : Nat) :
    FluxCut.localDivergence (fun x => cutPow x (n+1)) unitBracket
      = FluxCut.ofCut (constCut 1 1) :=
  (cutPow_calc n).mvt

/-- ★ Generic FTC bridge for x^(n+1) (∀ n). -/
theorem cutPow_calc_ftc (n : Nat) :
    FluxCut.localDivergence (fun x => cutPow x (n+1)) unitBracket
      = FluxCut.fluxAlong (fun x => cutPow x (n+1)) unitBracket :=
  (cutPow_calc n).ftc

/-- Phase BP capstone: cutPow_calc gives MVT + FTC for any n. -/
theorem cutPow_calc_capstone (n : Nat) :
    FluxCut.localDivergence (fun x => cutPow x (n+1)) unitBracket
        = FluxCut.ofCut (constCut 1 1)
    ∧ FluxCut.localDivergence (fun x => cutPow x (n+1)) unitBracket
        = FluxCut.fluxAlong (fun x => cutPow x (n+1)) unitBracket
    ∧ (fun x => cutPow x (n+1)) (constCut 0 1) = constCut 0 1
    ∧ (fun x => cutPow x (n+1)) (constCut 1 1) = constCut 1 1 :=
  ⟨cutPow_calc_mvt n, cutPow_calc_ftc n,
   (cutPow_calc n).pass.left, (cutPow_calc n).pass.right⟩

end ClassicCalc

end E213.Research.Real213.CutSum
