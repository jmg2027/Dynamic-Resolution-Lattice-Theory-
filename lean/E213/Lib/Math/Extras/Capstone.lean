import E213.Lib.Math.Extras.CauchySchwarz
import E213.Lib.Math.Extras.LpOneCollapse
import E213.Lib.Math.Extras.SymFin
import E213.Lib.Math.Extras.InnerCauchy

/-!
# Math Extras — Capstone synthesis (deferral cleanup)

4 cluster witnesses + total bundle.  All ∅-axiom.

This Capstone closes the four "honest scope" deferrals from the
2026-05-07 marathon block:
  * Measure / Functional Hölder atomic (Cauchy-Schwarz Nat-side)
  * Lp p=1 collapse (funext-free `∀ S` form)
  * Sₙ upgrade from `Nat → Nat` to `Fin n → Fin n`
  * Inner-product Cauchy-Schwarz at the `n=1` atomic level
-/

namespace E213.Lib.Math.Extras.Capstone

open E213.Lib.Math.Extras.CauchySchwarz (two_mul_le_sq_add_sq)
open E213.Lib.Math.Extras.LpOneCollapse (lp_one_eq_lebesgue)
open E213.Lib.Math.Extras.SymFin
  (FinPerm idPerm composeFin idPerm_at swap2 fin2_zero fin2_one
   swap2_zero swap2_one swap2_involutive_zero swap2_involutive_one)
open E213.Lib.Math.Extras.InnerCauchy (inner_cs_atomic)
open E213.Lib.Math.Functional.InnerProduct (innerNum)

/-- ★ **Cauchy-Schwarz / Hölder witness (Nat-side, ∀ a b)**. -/
theorem cs_witness (a b : Nat) :
    2 * (a * b) ≤ a * a + b * b :=
  two_mul_le_sq_add_sq a b

/-- ★ **Lp p=1 collapse witness (∀ S, funext-free)**. -/
theorem lp_one_witness (f : Nat → Nat)
    (s : List E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket.DyadicBracket) :
    E213.Lib.Math.Measure.Lp.lpNormPow 1 f s
      = E213.Lib.Math.Measure.LebesgueIntegral.lebesgueStepNum f s :=
  lp_one_eq_lebesgue f s

/-- ★ **Sₙ via Fin n witness** — id, swap2, involutive at 0/1. -/
theorem symFin_witness :
    swap2 fin2_zero = fin2_one
    ∧ swap2 fin2_one = fin2_zero
    ∧ composeFin swap2 swap2 fin2_zero = fin2_zero
    ∧ composeFin swap2 swap2 fin2_one = fin2_one :=
  ⟨swap2_zero, swap2_one,
   swap2_involutive_zero, swap2_involutive_one⟩

/-- ★ **Inner-product Cauchy-Schwarz atomic (n=1)**. -/
theorem inner_cs_witness (f g : Nat → Nat) :
    (innerNum 1 f g) * (innerNum 1 f g)
      = innerNum 1 f f * innerNum 1 g g :=
  inner_cs_atomic f g

/-- ★★★ **Total witness** ★★★ — 4-fact bundle bundling all four
    closed deferrals. -/
theorem total_witness (a b : Nat) (f g : Nat → Nat)
    (s : List E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket.DyadicBracket) :
    2 * (a * b) ≤ a * a + b * b
    ∧ E213.Lib.Math.Measure.Lp.lpNormPow 1 f s
        = E213.Lib.Math.Measure.LebesgueIntegral.lebesgueStepNum f s
    ∧ swap2 fin2_zero = fin2_one
    ∧ (innerNum 1 f g) * (innerNum 1 f g)
        = innerNum 1 f f * innerNum 1 g g :=
  ⟨two_mul_le_sq_add_sq a b, lp_one_eq_lebesgue f s,
   swap2_zero, inner_cs_atomic f g⟩

end E213.Lib.Math.Extras.Capstone
