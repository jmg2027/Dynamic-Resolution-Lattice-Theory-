import E213.Lib.Math.Measure.Lp
import E213.Lib.Math.Measure.LebesgueIntegral

/-!
# Lp p=1 collapse (∀ S, funext-free; ∅-axiom)

Closes the deferral noted in `Measure/INDEX.md`: the `∀ S` form of
`lpNormPow 1 f S = lebesgueStepNum f S` (per-bracket version was
preserved; the universal form was deferred because `congr+funext`
leaks `Quot.sound`).

This file proves it by direct *list induction* — no funext, no
Quot.sound, no propext.  Every step is term-mode `Nat`-arithmetic
on the explicit recursion.
-/

namespace E213.Lib.Math.Tactic.Extras.LpOneCollapse

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket
  (DyadicBracket DyadicBracket.midNum DyadicBracket.lenNum)
open E213.Lib.Math.Measure.MeasurableSet (DyadicMeasurableSet)
open E213.Lib.Math.Measure.LebesgueIntegral (lebesgueStepNum)
open E213.Lib.Math.Measure.Lp (lpNormPow powIntegrand)

/-- ★ `‖f‖_1 = ∫ f dμ` for *every* measurable set `S` (no funext). -/
theorem lp_one_eq_lebesgue : ∀ (f : Nat → Nat) (s : List DyadicBracket),
    lpNormPow 1 f s = lebesgueStepNum f s
  | _, [] => rfl
  | f, db :: rest => by
      show f db.midNum ^ 1 * db.lenNum
            + lpNormPow 1 f rest
          = f db.midNum * db.lenNum
            + lebesgueStepNum f rest
      rw [Nat.pow_one, lp_one_eq_lebesgue f rest]

end E213.Lib.Math.Tactic.Extras.LpOneCollapse
