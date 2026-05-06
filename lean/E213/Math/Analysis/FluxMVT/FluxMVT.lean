import E213.Math.Analysis.FluxMVT.FluxDivergence

import E213.Math.Real213.Core
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutSumTest
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
/-!
# FluxMVT
-4: **Mean Value Theorem** in flux form (concrete cases).

213-native MVT: localDivergence f db cohomologically matches
f.derivative at a trajectory midpoint.

The general statement requires the difference quotient bound theorem
(+).  This file establishes concrete cases:

  fluxBalance              : cohomological equality predicate
  mvt_const                : constants have balanced divergence
  mvt_id_unit_form         : id at unitBracket — explicit form
  localDivergence_id_form  : id divergence at any bracket
-/

namespace E213.Math.Analysis.FluxMVT.FluxMVT

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutPow (cutScale)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.CutContinuity (constCutFn)
open E213.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Math.Analysis.FluxMVT.FluxCochain.FluxCut
  (fluxAlong isBalanced fluxAlong_const_isBalanced)
open E213.Math.Analysis.FluxMVT.FluxDivergence.FluxCut
  (fluxScale localDivergence fluxScale_balanced
   localDivergence_const_balanced)
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory (unitBracket)

namespace FluxCut

/-- Cohomological equality: both components match pointwise.
    This IS the 213-native FluxCut equivalence (avoids struct equality
    which would require funext on the cut-function fields). -/
def fluxBalance (a b : FluxCut) : Prop :=
  ∀ m k, a.forward m k = b.forward m k ∧ a.backward m k = b.backward m k

/-- Alias for `fluxBalance` — cleaner name when used as cut-equality. -/
abbrev fluxCutEq := fluxBalance

/-- `fluxCutEq` derived from struct equality (PURE: no funext). -/
theorem fluxCutEq_of_eq {a b : FluxCut} (h : a = b) : fluxCutEq a b := by
  intro m k
  exact ⟨by rw [h], by rw [h]⟩

/-- MVT for constants: localDivergence balanced (∂c = 0). -/
theorem mvt_const (c : Nat → Nat → Bool) (db : DyadicBracket) :
    isBalanced (localDivergence (constCutFn c) db) :=
  localDivergence_const_balanced c db

/-- MVT for identity at unit bracket: explicit forward/backward form. -/
theorem mvt_id_unit_form :
    (localDivergence id unitBracket).forward
      = cutScale (2^0) 1 (constCut 1 1)
    ∧ (localDivergence id unitBracket).backward
      = cutScale (2^0) 1 (constCut 0 1) := ⟨rfl, rfl⟩

/-- Identity local divergence form at any bracket. -/
theorem localDivergence_id_form (db : DyadicBracket) :
    localDivergence id db
      = { forward := cutScale (2^db.expE) 1 db.rightCut,
          backward := cutScale (2^db.expE) 1 db.leftCut } := rfl

/-- fluxBalance is reflexive. -/
theorem fluxBalance_refl (a : FluxCut) : fluxBalance a a :=
  fun _ _ => ⟨rfl, rfl⟩

/-- fluxBalance is symmetric. -/
theorem fluxBalance_symm (a b : FluxCut) :
    fluxBalance a b → fluxBalance b a := by
  intro h m k
  exact ⟨(h m k).1.symm, (h m k).2.symm⟩

/-- fluxBalance is transitive. -/
theorem fluxBalance_trans {a b c : FluxCut}
    (hab : fluxBalance a b) (hbc : fluxBalance b c) : fluxBalance a c :=
  fun m k => ⟨(hab m k).1.trans (hbc m k).1,
              (hab m k).2.trans (hbc m k).2⟩

/-- Pointwise field projections to fluxCutEq. -/
theorem fluxCutEq_of_pointwise {a b : FluxCut}
    (hf : ∀ m k, a.forward m k = b.forward m k)
    (hb : ∀ m k, a.backward m k = b.backward m k) : fluxCutEq a b :=
  fun m k => ⟨hf m k, hb m k⟩

/-- Forward projection from fluxCutEq. -/
theorem fluxCutEq_forward {a b : FluxCut} (h : fluxCutEq a b) :
    ∀ m k, a.forward m k = b.forward m k :=
  fun m k => (h m k).1

/-- Backward projection from fluxCutEq. -/
theorem fluxCutEq_backward {a b : FluxCut} (h : fluxCutEq a b) :
    ∀ m k, a.backward m k = b.backward m k :=
  fun m k => (h m k).2

end FluxCut

end E213.Math.Analysis.FluxMVT.FluxMVT
