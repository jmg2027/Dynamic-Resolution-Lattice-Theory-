import E213.Research.Universal.QuotLens

/-!
# Research.FamilyMeet: slash-congruence meet of an arbitrary-index family

Generalizes the single-`E` form of `UniversalQuotLens` to a family
`⟨E_i⟩_{i ∈ I}`.  The cardinality of the index type `I` is arbitrary
(countable I in particular → the 213-internal counterpart of countable Choice).

## Core

If each E_i is a slash-congruence, then `λ r r'. ∀ i, E_i r r'` is
also a slash-congruence.  A single Lens captures that intersection
kernel via `universalLens`.

## Significance

Family version of the "Choice → Lens specification" from PAPER1 §5.1:
simultaneous representative selection for a countable family is possible
inside 213 via a single Lens — no external countable Choice required.
Formalization of the *complete meet-semilattice* structure of the
Lens-kernel space.
-/

namespace E213.Research.Lens.FamilyMeet

open E213.Firmware E213.Hypervisor
open E213.Research.Universal.QuotLens

/-- Index-wise intersection of a slash-congruence family. -/
def familyMeet {I : Type} (E : I → Raw → Raw → Prop)
    (r r' : Raw) : Prop :=
  ∀ i : I, E i r r'

theorem familyMeet_refl {I : Type} (E : I → Raw → Raw → Prop)
    (hrefl : ∀ i r, E i r r) (r : Raw) : familyMeet E r r :=
  fun i => hrefl i r

theorem familyMeet_symm {I : Type} (E : I → Raw → Raw → Prop)
    (hsymm : ∀ i r r', E i r r' → E i r' r) (r r' : Raw) :
    familyMeet E r r' → familyMeet E r' r :=
  fun h i => hsymm i r r' (h i)

theorem familyMeet_trans {I : Type} (E : I → Raw → Raw → Prop)
    (htrans : ∀ i r r' r'', E i r r' → E i r' r'' → E i r r'')
    (r r' r'' : Raw) :
    familyMeet E r r' → familyMeet E r' r'' → familyMeet E r r'' :=
  fun h1 h2 i => htrans i r r' r'' (h1 i) (h2 i)

theorem familyMeet_slash {I : Type} (E : I → Raw → Raw → Prop)
    (hslash : ∀ i (x x' y y' : Raw) (h : x ≠ y) (h' : x' ≠ y'),
              E i x x' → E i y y' → E i (Raw.slash x y h) (Raw.slash x' y' h'))
    (x x' y y' : Raw) (h : x ≠ y) (h' : x' ≠ y') :
    familyMeet E x x' → familyMeet E y y' →
    familyMeet E (Raw.slash x y h) (Raw.slash x' y' h') :=
  fun hxx hyy i => hslash i x x' y y' h h' (hxx i) (hyy i)

end E213.Research.Lens.FamilyMeet

namespace E213.Research.Lens.FamilyMeet

open E213.Firmware E213.Hypervisor
open E213.Research.Universal.QuotLens

/-- **Family meet via universalLens**: the simultaneous slash-congruence
    intersection of an arbitrary family `⟨E_i⟩_{i ∈ I}` can be
    expressed as the kernel of a single Lens.

    If each E_i is a slash-congruence (4 closure properties), then the
    kernel of universalLens (familyMeet E) equals exactly `familyMeet E`. -/
theorem familyMeet_kernel_eq
    {I : Type} (E : I → Raw → Raw → Prop)
    (hrefl : ∀ i r, E i r r)
    (hsymm : ∀ i r r', E i r r' → E i r' r)
    (htrans : ∀ i r r' r'', E i r r' → E i r' r'' → E i r r'')
    (hslash : ∀ i (x x' y y' : Raw) (h : x ≠ y) (h' : x' ≠ y'),
              E i x x' → E i y y' →
              E i (Raw.slash x y h) (Raw.slash x' y' h'))
    (r r' : Raw) :
    (universalLens (familyMeet E)).view r
      = (universalLens (familyMeet E)).view r'
      ↔ familyMeet E r r' :=
  universalLens_kernel_eq_E (familyMeet E)
    (familyMeet_refl E hrefl)
    (familyMeet_symm E hsymm)
    (familyMeet_trans E htrans)
    (familyMeet_slash E hslash) r r'

end E213.Research.Lens.FamilyMeet
