import E213.Lib.Math.Foundations.GodelArithmetic.AbstractProp

/-!
# Incompleteness ⊕ consistency — the formal trade-off (∅-axiom)

`AbstractProp.godel_inconsistency` shows: total Prop-valued
provability + diagonal property ⇒ `False`.

To recover real Gödel — *consistent ⇒ incomplete* — we need a
**partial** notion of provability (some sentences neither provable
nor refutable).  This file gives the proper structure.
-/

namespace E213.Lib.Math.Foundations.GodelArithmetic.IncompletenessVsConsistency

/-- A formal system with separate provability + refutability,
    consistency built in. -/
structure FormalSystem where
  Sent : Type
  Provable  : Sent → Prop
  Refutable : Sent → Prop
  consistent : ∀ s, ¬ (Provable s ∧ Refutable s)

/-- Completeness: every sentence is provable or refutable. -/
def IsComplete (FS : FormalSystem) : Prop :=
  ∀ s : FS.Sent, FS.Provable s ∨ FS.Refutable s

/-- A Gödel sentence: a sentence whose provability mirrors its
    own non-provability (the result of applying the diagonal
    lemma to `¬ Provable ·`). -/
def HasGodelSentence (FS : FormalSystem) : Prop :=
  ∃ φ : FS.Sent,
    (FS.Provable φ → FS.Refutable φ) ∧
    (FS.Refutable φ → FS.Provable φ)

/-- ★ **Trade-off theorem.**  A formal system with a Gödel
    sentence cannot be both consistent and complete. -/
theorem incompleteness_or_inconsistency
    (FS : FormalSystem) (h : HasGodelSentence FS) (hc : IsComplete FS) :
    False := by
  obtain ⟨φ, hpr, hre⟩ := h
  cases hc φ with
  | inl hp => exact FS.consistent φ ⟨hp, hpr hp⟩
  | inr hr => exact FS.consistent φ ⟨hre hr, hr⟩

/-- ★ **Contrapositive: consistent + Gödel sentence ⇒ incomplete.**
    A consistent system carrying a Gödel sentence has at least one
    undecided sentence. -/
theorem consistent_with_godel_implies_incomplete
    (FS : FormalSystem) (h : HasGodelSentence FS) :
    ¬ IsComplete FS :=
  fun hc => incompleteness_or_inconsistency FS h hc

/-- ★★★ **Real Gödel framing capstone.**  Two ∅-axiom facts:

    1. *Total* provability + diagonal ⇒ inconsistent
       (`AbstractProp.godel_inconsistency`).
    2. *Partial* provability + Gödel sentence + completeness ⇒
       inconsistent (this file).

    Together: a consistent system strong enough to carry a Gödel
    sentence is *necessarily incomplete* — some sentence is
    neither provable nor refutable. -/
theorem real_godel_capstone (FS : FormalSystem) (h : HasGodelSentence FS) :
    ¬ IsComplete FS :=
  consistent_with_godel_implies_incomplete FS h

end E213.Lib.Math.Foundations.GodelArithmetic.IncompletenessVsConsistency
