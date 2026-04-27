import E213.Research.UniversalQuotLens

/-!
# Research.FamilyMeet: arbitrary-index family 의 slash-congruence meet

`UniversalQuotLens` 의 single-`E` form 을 family `⟨E_i⟩_{i ∈ I}`
로 일반화.  Index type `I` 의 cardinality 가 임의 (특히
countable I 가능 → countable Choice 의 213-internal counterpart).

## 핵심

각 E_i 가 slash-congruence 면 `λ r r'. ∀ i, E_i r r'` 도
slash-congruence.  `universalLens` 로 단일 Lens 가 그
intersection kernel 을 capture.

## 의의

PAPER1 §5.1 의 "Choice → Lens specification" 의 family
version: countable family 의 simultaneous representative
selection 이 213 안 에서 single Lens 로 가능 — external
countable Choice 부재.  Lens-kernel space 의 *complete
meet-semilattice* structure 의 형식 화.
-/

namespace E213.Research.FamilyMeet

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- Index 별 slash-congruence family 의 intersection. -/
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

end E213.Research.FamilyMeet

namespace E213.Research.FamilyMeet

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- **Family meet via universalLens**: arbitrary family
    `⟨E_i⟩_{i ∈ I}` 의 simultaneous slash-congruence
    intersection 이 single Lens 의 kernel 로 표현 가능.

    각 E_i 가 slash-congruence (4 closure properties)
    이면 universalLens (familyMeet E) 의 kernel 이 정확 히
    `familyMeet E`. -/
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

end E213.Research.FamilyMeet
