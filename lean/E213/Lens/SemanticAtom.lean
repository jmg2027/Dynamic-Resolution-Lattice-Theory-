import E213.Lens.LensCore
import E213.Lens.Initiality
import E213.Lens.Morphism.FoldStructured
import E213.Lens.Morphism.DepthParityNotFold

/-!
# SemanticAtom: 213 = the atom of meaning (formal hub)

Hub for the formalization of Note 75's thesis.  Clarifies that all previous
vague framings (constructive subset, fold-structured, scale-invariance)
are specific aspects of this thesis.

## Thesis (Mingu, 2026-04-25)

> Nothing with meaning can escape 213.  213 is the semantic atom.
> Nothing is more primitive than the axiom of 213.
> Everything is inside, a representation of, and a boundary of the 213 atom.

## Formal layer

| Layer | Lean form |
|-------|-----------|
| Distinguishing framework abstraction | `HasDistinguishing` typeclass |
| Raw as instance | `Raw.instHasDistinguishing` |
| Universal morphism | `Raw.fold` (already exists) |
| Initial object | RawInitiality.lean (existing) |
| Strict minimum | AxiomMinimality.lean (4 cases) |

## Lean formalization of the thesis

This file uses the `HasDistinguishing` typeclass to make explicit the
abstraction of the meaning framework — Raw is the strict minimum of this
abstraction (the 4 cases of AxiomMinimality are the negative direction).
-/

namespace E213.Lens.SemanticAtom

open E213.Theory E213.Lens

/-! ### HasDistinguishing typeclass — abstraction of the meaning framework

Minimum requirements for a "framework with meaning":
1. Two distinguishable base elements (a ≠ b).
2. A combining operation (binary).
3. Symmetry of combine (swap-invariance) — commutativity of slash.

Without (3), encoding artifacts leak into results — Raw axiom's
slash_comm.  Therefore it is part of the meaning framework. -/

class HasDistinguishing (α : Type) where
  a : α
  b : α
  distinct : a ≠ b
  combine : α → α → α
  combine_sym : ∀ x y, combine x y = combine y x

end E213.Lens.SemanticAtom

namespace E213.Lens.SemanticAtom

open E213.Theory E213.Lens

/-! ### Raw as HasDistinguishing instance

The most trivial instance: Raw's a, b, slash themselves satisfy the axioms.
slash_comm directly preserves combine_sym. -/

instance : HasDistinguishing Raw where
  a := Raw.a
  b := Raw.b
  distinct := by decide
  combine x y := if h : x = y then x else Raw.slash x y h
  combine_sym x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
      apply Raw.slash_comm

end E213.Lens.SemanticAtom

namespace E213.Lens.SemanticAtom

open E213.Theory E213.Lens

/-! ### Universal morphism: Raw → α (HasDistinguishing α)

For an instance of `HasDistinguishing α`, Raw embeds via a unique
morphism.  fold is the universal morphism — Raw is the initial object
in the "distinguishing framework" category.

(That is, the 213 axiom is the minimum for *every* meaning framework.) -/

/-- Universal morphism Raw → α via fold. -/
def universalMorphism (α : Type) [d : HasDistinguishing α] : Raw → α :=
  Raw.fold d.a d.b d.combine

/-- Universal morphism preserves a. -/
theorem universalMorphism_a (α : Type) [d : HasDistinguishing α] :
    universalMorphism α Raw.a = d.a := rfl

/-- Universal morphism preserves b. -/
theorem universalMorphism_b (α : Type) [d : HasDistinguishing α] :
    universalMorphism α Raw.b = d.b := rfl

/-- Universal morphism preserves slash via fold_slash. -/
theorem universalMorphism_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    universalMorphism α (Raw.slash x y h)
      = d.combine (universalMorphism α x) (universalMorphism α y) := by
  unfold universalMorphism
  apply Raw.fold_slash _ _ _ d.combine_sym

end E213.Lens.SemanticAtom

namespace E213.Lens.SemanticAtom

open E213.Theory E213.Lens

/-! ### Lens as a specific instance of HasDistinguishing

The view of Lens α is a morphism of HasDistinguishing α — that is,
Lens is a specific form of an instance of the meaning framework.
Raw is the carrier (universal) for all Lenses. -/

/-- Lens as a HasDistinguishing instance — takes distinctness of base
    and swap-sym of combine as hypotheses.  A general Lens can have
    degenerate cases like constLens where distinguishing is absent
    (base_a = base_b), so only distinguishing-preserving Lenses are instances.

    This partial functoriality is the formal expression of "the atom of
    meaning is Raw, and Lens is its representation on top". -/
def lensToHasDistinguishing {α : Type} (L : Lens α)
    (h_distinct : L.base_a ≠ L.base_b)
    (h_sym : ∀ u v, L.combine u v = L.combine v u) :
    HasDistinguishing α where
  a := L.base_a
  b := L.base_b
  distinct := h_distinct
  combine := L.combine
  combine_sym := h_sym

end E213.Lens.SemanticAtom

namespace E213.Lens.SemanticAtom

open E213.Theory E213.Lens
open E213.Lens.Morphism.FoldStructured

/-! ### Negative direction: boundary of Lens-expressibility

Dual of §1.1 (formal core).  If the `HasDistinguishing` typeclass
is the positive form of "abstraction of the meaning framework", then
the following is the negative form: **existence of functions not
expressible inside the framework**.

Specific instances have already been formalized in
`Hypervisor/Lens/Morphism/{NoDepthParity, DepthParityNotFold, SlashCharNotFold}.lean`.
Here we state the unified statement — Lens-expressibility has a
non-trivial boundary (not every Raw → α function is Lens-expressible).

Unified analysis of Note 77. -/

/-- Precise definition of **Lens-expressible**: f is the view of some Lens L
    (assuming swap-symmetry of combine). -/
def IsLensExpressible {α : Type} (f : Raw → α) : Prop :=
  ∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧
                (∀ r, L.view r = f r)

/-- IsLensExpressible ↔ FoldStructured.  FoldStructured.lean
    Wrapping of the result from FoldStructured.lean. -/
theorem isLensExpressible_iff_foldStructured {α : Type} (f : Raw → α) :
    IsLensExpressible f ↔ FoldStructured f := by
  unfold IsLensExpressible
  constructor
  · rintro ⟨L, hsym, hview⟩
    obtain ⟨ba, bb, c, hba, hbb, hcs, hslash⟩ :=
      lens_view_fold_structured L hsym
    refine ⟨ba, bb, c, ?_, ?_, hcs, ?_⟩
    · rw [← hview Raw.a]; exact hba
    · rw [← hview Raw.b]; exact hbb
    · intro x y h
      rw [← hview (Raw.slash x y h), ← hview x, ← hview y]
      exact hslash x y h
  · intro hfs
    obtain ⟨L, hsym, hview⟩ := fold_structured_lens_expressible f hfs
    exact ⟨L, hsym, hview⟩

/-- **Negative existence**: ∃ f : Raw → Bool, f is not Lens-expressible.
    Direct evidence for the boundary of the semantic atom thesis. -/
theorem exists_non_lens_expressible :
    ∃ f : Raw → Bool, ¬ IsLensExpressible f := by
  refine ⟨E213.Lens.Morphism.DepthParityNotFold.depthParityFn, ?_⟩
  intro hLE
  exact E213.Lens.Morphism.DepthParityNotFold.depthParityFn_not_fold_structured
    ((isLensExpressible_iff_foldStructured _).mp hLE)

end E213.Lens.SemanticAtom

namespace E213.Lens.SemanticAtom

open E213.Theory E213.Lens
open E213.Lens.Initiality

/-! ### Universal property of `HasDistinguishing` category

HasDistinguishing-level restatement of `Lens.initiality` (RawInitiality.lean).
Explicit ∃! statement that Raw is the *initial object* of the
distinguishing-framework category. -/

/-- **Universal morphism uniqueness**: for an instance of HasDistinguishing α,
    the distinguishing-preserving function Raw → α is exactly
    `universalMorphism α`. -/
theorem universalMorphism_unique (α : Type) [d : HasDistinguishing α]
    (f : Raw → α)
    (ha : f Raw.a = d.a)
    (hb : f Raw.b = d.b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = d.combine (f x) (f y)) :
    ∀ r : Raw, f r = universalMorphism α r := by
  intro r
  exact Lens.view_unique
    (⟨d.a, d.b, d.combine⟩ : Lens α) d.combine_sym f ha hb hslash r

/-- **Raw as initial object of HasDistinguishing-category**:
    for any instance α, the distinguishing-preserving function
    Raw → α *uniquely* exists (= `universalMorphism α`).
    This is the categorical statement of "the 213 axiom is the minimum
    for every meaning framework".  Uniqueness stated **pointwise**
    (`∀ r, g r = f r`) instead of as function equality, to avoid
    funext (= Quot.sound).  (∃! syntax absent in Lean 4 core; expressed
    as explicit existence + uniqueness conjunction.) -/
theorem raw_initial (α : Type) [d : HasDistinguishing α] :
    ∃ f : Raw → α,
      (f Raw.a = d.a) ∧
      (f Raw.b = d.b) ∧
      (∀ (x y : Raw) (h : x ≠ y),
        f (Raw.slash x y h) = d.combine (f x) (f y)) ∧
      (∀ g : Raw → α,
        g Raw.a = d.a →
        g Raw.b = d.b →
        (∀ (x y : Raw) (h : x ≠ y),
          g (Raw.slash x y h) = d.combine (g x) (g y)) →
        ∀ r : Raw, g r = f r) := by
  refine ⟨universalMorphism α, ?_, ?_, ?_, ?_⟩
  · exact universalMorphism_a α
  · exact universalMorphism_b α
  · intro x y h; exact universalMorphism_slash α x y h
  · intro g hga hgb hgslash r
    exact universalMorphism_unique α g hga hgb hgslash r

end E213.Lens.SemanticAtom
