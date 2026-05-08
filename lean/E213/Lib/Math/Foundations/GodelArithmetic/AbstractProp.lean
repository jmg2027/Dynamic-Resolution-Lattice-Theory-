/-!
# Abstract Prop-level Gödel inconsistency (∅-axiom)

The Prop-form of Gödel's first incompleteness — *cleaner* than the
Bool form (`UniverseChain.Godel`) because it works directly with
intuitionistic Prop reasoning, no `Bool`-coding needed.

## Statement

An *abstract formal system* is a type `Sent` of sentences plus a
provability predicate `Prov : Sent → Prop`.  It satisfies the
**diagonal property** if every `Sent → Prop` predicate has a
self-asserting sentence:

    ∀ P : Sent → Prop, ∃ φ : Sent, Prov φ ↔ P φ.

**Theorem.**  Any abstract formal system with the diagonal
property is inconsistent (proves `False`).

## Proof sketch

Apply the diagonal to `P := λ s, ¬ Prov s`.  Get `φ` with
`Prov φ ↔ ¬ Prov φ`.  Standard Prop-level argument:

  * `Prov φ → ¬ Prov φ` (forward), so `¬ Prov φ`.
  * Then `Prov φ` (backward applied to `¬ Prov φ`).
  * Contradiction.

## ∅-axiom

Pure intuitionistic Prop manipulation: `Iff.mp`, `Iff.mpr`,
existence destructuring.  No `propext`, no `Quot.sound`, no
`Classical`.
-/

namespace E213.Lib.Math.Foundations.GodelArithmetic.AbstractProp

/-- An abstract formal system: type of sentences plus a Prop-valued
    provability predicate. -/
structure FormalSystem where
  Sent : Type
  Prov : Sent → Prop

/-- The diagonal property: every predicate has a self-asserting sentence. -/
def HasDiagonal (FS : FormalSystem) : Prop :=
  ∀ P : FS.Sent → Prop, ∃ φ : FS.Sent, FS.Prov φ ↔ P φ

/-- ★★★ **Gödel inconsistency (Prop form).**  An abstract formal
    system with the diagonal property proves `False`. -/
theorem godel_inconsistency (FS : FormalSystem)
    (h : HasDiagonal FS) : False :=
  match h (fun s => ¬ FS.Prov s) with
  | ⟨_, hφ⟩ =>
      let not_prov : ¬ FS.Prov _ := fun hp => hφ.mp hp hp
      not_prov (hφ.mpr not_prov)

end E213.Lib.Math.Foundations.GodelArithmetic.AbstractProp
