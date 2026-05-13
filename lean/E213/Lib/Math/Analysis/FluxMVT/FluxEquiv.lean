import E213.Lib.Math.Analysis.FluxMVT.FluxCut
import E213.Lib.Math.Real213.Core.Core.CutPoset

import E213.Lib.Math.Real213.Core.Core
/-!
# FluxEquiv
-1: **Cohomological equivalence** for FluxCut as a Setoid
(no Quotient — preserve 213 ontology).

Two FluxCuts are cohomologically equivalent when their forward and
backward components agree pointwise via `cutEq`:

  a ≈ b ↔ cutEq a.forward b.forward ∧ cutEq a.backward b.backward

This is the Setoid that bridges *propositional* equality to dyadic
*pointwise* equality without collapsing structure (no Quot.mk).

## Theorems

  cohomEquiv             : equivalence relation predicate
  cohomEquiv_refl/symm/trans : reflexive, symmetric, transitive
  fluxCutSetoid          : Setoid instance
  cohomEquiv_of_eq       : propositional eq implies cohomEquiv
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxEquiv

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Core.Core.CutPoset (cutEq cutEq_trans cutEq_refl cutEq_symm)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut (FluxCut)
open E213.Lib.Math.Analysis.FluxMVT.FluxCut.FluxCut (add neg)

namespace FluxCut

/-- **Cohomological equivalence**: forward and backward components
    are pointwise cutEq.  This is the 213-native form of "equality"
    on flux structures — preserves orientation distinction without
    collapsing to propositional equality. -/
def cohomEquiv (a b : FluxCut) : Prop :=
  cutEq a.forward b.forward ∧ cutEq a.backward b.backward

theorem cohomEquiv_refl (a : FluxCut) : cohomEquiv a a :=
  ⟨cutEq_refl a.forward, cutEq_refl a.backward⟩

theorem cohomEquiv_symm (a b : FluxCut) : cohomEquiv a b → cohomEquiv b a
  | ⟨hf, hb⟩ => ⟨cutEq_symm _ _ hf, cutEq_symm _ _ hb⟩

theorem cohomEquiv_trans (a b c : FluxCut) :
    cohomEquiv a b → cohomEquiv b c → cohomEquiv a c
  | ⟨hf₁, hb₁⟩, ⟨hf₂, hb₂⟩ =>
    ⟨cutEq_trans _ _ _ hf₁ hf₂, cutEq_trans _ _ _ hb₁ hb₂⟩

/-- Setoid instance for FluxCut via cohomEquiv. -/
instance fluxCutSetoid : Setoid FluxCut where
  r := cohomEquiv
  iseqv := ⟨cohomEquiv_refl, fun {a b} => cohomEquiv_symm a b,
            fun {a b c} => cohomEquiv_trans a b c⟩

/-- Propositional equality implies cohomEquiv (trivially). -/
theorem cohomEquiv_of_eq (a b : FluxCut) (h : a = b) : cohomEquiv a b := by
  subst h; exact cohomEquiv_refl a

/-- Notation: a ≈ b for cohomEquiv a b (via Setoid). -/
example (a : FluxCut) : a ≈ a := cohomEquiv_refl a

end FluxCut

end E213.Lib.Math.Analysis.FluxMVT.FluxEquiv
