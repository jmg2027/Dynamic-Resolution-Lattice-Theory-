import E213.Hypervisor.Lens

/-!
# Research.Prism: categorical dual of Lens

User directive (2026-04-25): "bring the Prism concept (dual of Lens)
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

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

/-- 213-style Prism: categorical dual of Lens.

    `preview` is the partial extraction of a specific case.
    `review` is the constructor for that case's elements.
    coherence is the round-trip property. -/
structure Prism (α : Type) where
  preview : Raw → Option α
  review : α → Raw
  coherence : ∀ a, preview (review a) = some a

end E213.Research.Prism

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

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

end E213.Research.Prism

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

/-- aPrism preview is some at Raw.a and none at Raw.b. -/
theorem aPrism_a : aPrism.preview Raw.a = some () := by
  unfold aPrism caseElement
  show (if (Raw.a : Raw) = Raw.a then some () else none) = some ()
  rw [if_pos rfl]

theorem aPrism_b : aPrism.preview Raw.b = none := by
  unfold aPrism caseElement
  show (if (Raw.b : Raw) = Raw.a then some () else none) = none
  rw [if_neg (by decide)]

theorem bPrism_a : bPrism.preview Raw.a = none := by
  unfold bPrism caseElement
  show (if (Raw.a : Raw) = Raw.b then some () else none) = none
  rw [if_neg (by decide)]

theorem bPrism_b : bPrism.preview Raw.b = some () := by
  unfold bPrism caseElement
  show (if (Raw.b : Raw) = Raw.b then some () else none) = some ()
  rw [if_pos rfl]

end E213.Research.Prism

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

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
  unfold caseElement at h1 h2
  show False
  -- preview r = if r = target then some () else none.
  by_cases ht1 : r = target1
  · -- r = target1.
    by_cases ht2 : r = target2
    · -- r = target2 also.  target1 = target2 contradiction.
      rw [← ht1, ht2] at h
      exact h rfl
    · -- r ≠ target2 → preview target2 r = none → contradicts h2.
      simp [ht2] at h2
  · -- r ≠ target1 → preview target1 r = none → contradicts h1.
    simp [ht1] at h1

/-- Specific instance: disjointness of aPrism and bPrism. -/
theorem aPrism_bPrism_disjoint (r : Raw) :
    ¬ (aPrism.preview r = some () ∧ bPrism.preview r = some ()) :=
  caseElement_disjoint Raw.a Raw.b (by decide) r

end E213.Research.Prism
