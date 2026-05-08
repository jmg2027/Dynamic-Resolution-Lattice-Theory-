import E213.Lib.Math.Foundations.GodelArithmetic.AbstractProp
import E213.Lib.Math.Foundations.GodelArithmetic.IncompletenessVsConsistency
import E213.Lib.Math.Foundations.GodelArithmetic.Formula

/-!
# Gödel marathon — Phase 1 capstone (∅-axiom)

  * `AbstractProp` — Prop-level abstract Gödel: total provability +
    diagonal ⇒ inconsistent.
  * `IncompletenessVsConsistency` — partial provability formulation:
    consistent + Gödel sentence ⇒ incomplete.
  * `Formula` — concrete formula syntax + Gödel-numbering shape
    (Phase 2 will prove injectivity + diagonal lemma).

## Phase 1 — proven (∅-axiom)

  * `AbstractProp.godel_inconsistency`
  * `IncompletenessVsConsistency.real_godel_capstone`
  * `Formula.depth/leafCount/encode_*`

## Phase 2 — left

  * Injectivity of `Formula.encode`.
  * Substitution + diagonal-construction function.
  * Diagonal lemma for concrete `Formula`.
  * Explicit Gödel sentence + applied incompleteness theorem.
-/

namespace E213.Lib.Math.Foundations.GodelArithmetic.Capstone

/-- ★ Phase 1: abstract Gödel at Prop level. -/
theorem phase1_abstract_godel
    (FS : AbstractProp.FormalSystem)
    (h : AbstractProp.HasDiagonal FS) : False :=
  AbstractProp.godel_inconsistency FS h

/-- ★ Phase 1: real-Gödel framing. -/
theorem phase1_real_godel
    (FS : IncompletenessVsConsistency.FormalSystem)
    (h : IncompletenessVsConsistency.HasGodelSentence FS) :
    ¬ IncompletenessVsConsistency.IsComplete FS :=
  IncompletenessVsConsistency.real_godel_capstone FS h

/-- ★ Phase 1: concrete syntax. -/
theorem phase1_formula_syntax :
    Formula.Formula.depth (Formula.Formula.atom 0) = 0
    ∧ Formula.Formula.leafCount (Formula.Formula.atom 0) = 1
    ∧ Formula.Formula.encode (Formula.Formula.atom 0) = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- ★★★ **Phase 1 capstone.** -/
theorem phase1_capstone :
    (∀ FS : AbstractProp.FormalSystem,
        AbstractProp.HasDiagonal FS → False)
    ∧ (∀ FS : IncompletenessVsConsistency.FormalSystem,
        IncompletenessVsConsistency.HasGodelSentence FS
        → ¬ IncompletenessVsConsistency.IsComplete FS)
    ∧ (Formula.Formula.depth (Formula.Formula.atom 0) = 0) :=
  ⟨AbstractProp.godel_inconsistency,
   IncompletenessVsConsistency.real_godel_capstone,
   rfl⟩

end E213.Lib.Math.Foundations.GodelArithmetic.Capstone
