import E213.Lib.Math.UniverseChain.Lawvere
import E213.Theory.Raw

/-!
# Gödel's First Incompleteness — abstract form (∅-axiom)

For any type `X` (sentences), `Pr : X → Bool` (decision /
provability), and `Repr : (X → Bool) → X` satisfying the
**diagonal correctness** condition

    ∀ f : X → Bool,  Pr (Repr f) = f (Repr f),

the system is **inconsistent** (proves `False`).

## Interpretation

Any consistent system that classifies sentences as a type with a
Boolean decision procedure `Pr` **cannot internally represent all
predicates on its sentences via `Repr_correct`** — the diagonal
lemma's full strength + completeness is contradictory.

## Caveat (meta vs internal)

This is the *abstract / Lawvere* form.  Real Gödel I for arithmetic
requires Gödel numbering + provability predicate proven to satisfy
the diagonal lemma — a separate marathon.  What this file gives:
the **mechanism** is ∅-axiom proven; any concrete system meeting
the hypotheses inherits the conclusion.

## ∅-axiom

Reduces to `not_has_no_fixed_point` from `UniverseChain.Lawvere`.
-/

namespace E213.Lib.Math.UniverseChain.Godel

open E213.Lib.Math.UniverseChain.Lawvere (not_has_no_fixed_point)

/-- **Abstract Gödel inconsistency.**  A Boolean decision procedure
    satisfying diagonal correctness on a representation function is
    contradictory. -/
theorem godel_inconsistency {X : Type}
    (Pr : X → Bool)
    (Repr : (X → Bool) → X)
    (Repr_correct : ∀ f : X → Bool, Pr (Repr f) = f (Repr f))
    : False :=
  let f : X → Bool := fun x => !(Pr x)
  not_has_no_fixed_point ⟨Pr (Repr f), (Repr_correct f).symm⟩

/-- **Tarski's undefinability of truth (abstract).**  No truth
    predicate `T : X → Bool` can correctly evaluate every
    representable predicate at its representation. -/
theorem tarski_undefinability {X : Type}
    (Repr : (X → Bool) → X) :
    ¬ ∃ T : X → Bool, ∀ f : X → Bool, T (Repr f) = f (Repr f) :=
  fun ⟨T, hT⟩ => godel_inconsistency T Repr hT

end E213.Lib.Math.UniverseChain.Godel

namespace E213.Lib.Math.UniverseChain.Godel

/-- **Gödel-style incompleteness for Raw.**  No combination of
    Boolean decision predicate `Pr : Raw → Bool` and representation
    function `Repr : (Raw → Bool) → Raw` with diagonal correctness
    can exist on `Raw`. -/
theorem godel_for_raw
    (Pr : E213.Theory.Raw → Bool)
    (Repr : (E213.Theory.Raw → Bool) → E213.Theory.Raw)
    (Repr_correct : ∀ f : E213.Theory.Raw → Bool,
                      Pr (Repr f) = f (Repr f))
    : False :=
  godel_inconsistency Pr Repr Repr_correct

/-- **No self-referential decision on Raw.**  For any Boolean
    decision procedure `Pr : Raw → Bool`, no representation
    function with diagonal correctness can exist. -/
theorem no_self_referential_decision
    (Pr : E213.Theory.Raw → Bool) :
    ¬ ∃ Repr : (E213.Theory.Raw → Bool) → E213.Theory.Raw,
        ∀ f : E213.Theory.Raw → Bool, Pr (Repr f) = f (Repr f) :=
  fun ⟨Repr, hR⟩ => godel_for_raw Pr Repr hR

/-- ★★★ **Capstone — abstract Gödel-incompleteness for 213.**

    Three ∅-axiom impossibilities, each Lawvere instance:

    1. `godel_inconsistency` — abstract form (any X).
    2. `tarski_undefinability` — no internal truth predicate.
    3. `no_self_referential_decision` — Raw-specialised. -/
theorem godel_capstone :
    (∀ {X : Type} (Pr : X → Bool) (Repr : (X → Bool) → X),
        (∀ f, Pr (Repr f) = f (Repr f)) → False)
    ∧ (∀ {X : Type} (Repr : (X → Bool) → X),
        ¬ ∃ T : X → Bool, ∀ f, T (Repr f) = f (Repr f))
    ∧ (∀ (Pr : E213.Theory.Raw → Bool),
        ¬ ∃ Repr : (E213.Theory.Raw → Bool) → E213.Theory.Raw,
            ∀ f, Pr (Repr f) = f (Repr f)) :=
  ⟨@godel_inconsistency, @tarski_undefinability,
   no_self_referential_decision⟩

end E213.Lib.Math.UniverseChain.Godel
