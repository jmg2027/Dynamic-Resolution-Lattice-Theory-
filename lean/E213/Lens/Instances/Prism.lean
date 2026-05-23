import E213.Lens.LensCore

/-!
# Prism: categorical dual of Lens

User directive: "bring the Prism concept (dual of Lens)
into the 213 grammar and build the algebraic dual."

The 213-form of the functional-programming Prism:
- `preview : Raw → Option α` (partial getter).
- `review : α → Raw` (constructor / injection).
- coherence: preview after review is a round-trip.

## Significance

Lens views *every* element of Raw as α (total).
Prism extracts only *specific cases* of Raw as α (partial) and
injects elements of α back into Raw (constructor).

→ Lens = product accessor, Prism = sum/coproduct accessor.

## Concrete instances

- `aPrism : Prism Unit` — case of Raw.a.
- `bPrism : Prism Unit` — case of Raw.b.

Each prism extracts a specific element of Raw *distinguishably*.
-/

namespace E213.Lens.Instances.Prism

open E213.Theory E213.Lens

/-- 213-style Prism: categorical dual of Lens.

    `preview` is the partial extraction of a specific case.
    `review` is the constructor for that case's elements.
    coherence is the round-trip property. -/
structure Prism (α : Type) where
  preview : Raw → Option α
  review : α → Raw
  coherence : ∀ a, preview (review a) = some a


/-- Specific case Prism from decidable equality on Raw. -/
def caseElement (target : Raw) : Prism Unit where
  preview r := if r = target then some () else none
  review _ := target
  coherence := fun _ => by
    show (if target = target then some () else none) = some ()
    rw [if_pos rfl]

/-- Case Prism for Raw.a. -/
def aPrism : Prism Unit := caseElement Raw.a

/-- Case Prism for Raw.b. -/
def bPrism : Prism Unit := caseElement Raw.b


/-! ### Generic preview truth table

The 4 truth-table entries below (`aPrism_a/b`, `bPrism_a/b`) all
follow from two generic lemmas about `caseElement` — preview on the
target yields `some`, preview on any other Raw yields `none`.

This is the Prism analogue of "decidable-eq dispatches to itself
vs other"; the truth table is forced by the `preview r := if r = target`
shape. -/

/-- `caseElement target` previews `target` as `some ()`. -/
theorem caseElement_preview_self (target : Raw) :
    (caseElement target).preview target = some () := by
  show (if target = target then some () else none) = some ()
  rw [if_pos rfl]

/-- `caseElement target` previews any other `r ≠ target` as `none`. -/
theorem caseElement_preview_other (target r : Raw) (h : r ≠ target) :
    (caseElement target).preview r = none := by
  show (if r = target then some () else none) = none
  rw [if_neg h]

/-- aPrism preview is some at Raw.a and none at Raw.b. -/
theorem aPrism_a : aPrism.preview Raw.a = some () :=
  caseElement_preview_self Raw.a

theorem aPrism_b : aPrism.preview Raw.b = none :=
  caseElement_preview_other Raw.a Raw.b (by decide)

theorem bPrism_a : bPrism.preview Raw.a = none :=
  caseElement_preview_other Raw.b Raw.a (by decide)

theorem bPrism_b : bPrism.preview Raw.b = some () :=
  caseElement_preview_self Raw.b


/-! ### Disjointness of Prisms (categorical universal property)

Case prisms for two different targets are mutually exclusive — the
direct form of the disjoint property of coproducts.

This is the structural evidence of Prism as a *coproduct accessor* —
strict disjointness of the categorical sum. -/

theorem caseElement_disjoint (target1 target2 : Raw) (h : target1 ≠ target2)
    (r : Raw) :
    ¬ ((caseElement target1).preview r = some () ∧
       (caseElement target2).preview r = some ()) := by
  intro ⟨h1, h2⟩
  show False
  by_cases ht1 : r = target1
  · by_cases ht2 : r = target2
    · -- r = target1 ∧ r = target2 → target1 = target2 contradiction.
      rw [← ht1, ht2] at h
      exact h rfl
    · -- r ≠ target2 → preview target2 r = none → contradicts h2
      have h2_form : (if r = target2 then some () else none : Option Unit)
                   = some () := h2
      rw [if_neg ht2] at h2_form
      exact Option.noConfusion h2_form
  · -- r ≠ target1 → preview target1 r = none → contradicts h1
    have h1_form : (if r = target1 then some () else none : Option Unit)
                 = some () := h1
    rw [if_neg ht1] at h1_form
    exact Option.noConfusion h1_form

/-- Specific instance: disjointness of aPrism and bPrism. -/
theorem aPrism_bPrism_disjoint (r : Raw) :
    ¬ (aPrism.preview r = some () ∧ bPrism.preview r = some ()) :=
  caseElement_disjoint Raw.a Raw.b (by decide) r

end E213.Lens.Instances.Prism
