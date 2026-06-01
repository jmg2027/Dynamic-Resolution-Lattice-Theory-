import E213.Lens.Universal.QuotLens

/-!
# FamilyJoin: slash-congruence join of an arbitrary-index family

Dual of `FamilyMeet`: the *smallest* slash-congruence containing all
`E_i` for an arbitrary-index family `⟨E_i⟩_{i ∈ I}`.

## Construction

`FamilyJoinEquiv E` is an inductive Prop carrying the generated
relation from family elements + equivalence-closure + slash-closure.
Realized as a single Lens kernel via `universalLens`.

## Significance

Together with `LensMeet` (binary meet), `JoinEquiv` (binary join),
and `FamilyMeet` (arbitrary meet), this completes the formalization
of the complete-lattice structure: the set of slash-congruences is a
*complete lattice*.
-/

namespace E213.Lens.Lattice.FamilyJoin

open E213.Theory E213.Lens
open E213.Lens.Universal.QuotLens

/-- Index-wise family join: smallest slash-congruence
    containing all `E i`. -/
inductive FamilyJoinEquiv {I : Type} (E : I → Raw → Raw → Prop) :
    Raw → Raw → Prop where
  | ofI (i : I) {x y : Raw} : E i x y → FamilyJoinEquiv E x y
  | refl (x : Raw) : FamilyJoinEquiv E x x
  | symm {x y : Raw} : FamilyJoinEquiv E x y → FamilyJoinEquiv E y x
  | trans {x y z : Raw} :
      FamilyJoinEquiv E x y → FamilyJoinEquiv E y z →
      FamilyJoinEquiv E x z
  | slash_cong {x x' y y' : Raw} (h : x ≠ y) (h' : x' ≠ y') :
      FamilyJoinEquiv E x x' → FamilyJoinEquiv E y y' →
      FamilyJoinEquiv E (Raw.slash x y h) (Raw.slash x' y' h')


/-- **Family join via universalLens**: the join of an arbitrary family
    is expressed as the kernel of a single Lens.  FamilyJoinEquiv
    inductively carries the 4 closure properties itself, so it satisfies
    the hypotheses of universalLens. -/
def familyJoinLens {I : Type} (E : I → Raw → Raw → Prop) :
    Lens (Raw → Prop) :=
  universalLens (FamilyJoinEquiv E)

theorem familyJoinLens_kernel {I : Type} (E : I → Raw → Raw → Prop)
    (r r' : Raw) :
    (familyJoinLens E).equivR r r' ↔ FamilyJoinEquiv E r r' :=
  universalLens_kernel_eq_E_R (FamilyJoinEquiv E)
    FamilyJoinEquiv.refl
    (fun _ _ h => FamilyJoinEquiv.symm h)
    (fun _ _ _ h1 h2 => FamilyJoinEquiv.trans h1 h2)
    (fun _ _ _ _ h h' h1 h2 => FamilyJoinEquiv.slash_cong h h' h1 h2)
    r r'

/-- **Universal property**: each E_i is contained in the family join.  Stated as
    `equivR` (pointwise `↔`), ∅-axiom. -/
theorem familyJoin_contains {I : Type} (E : I → Raw → Raw → Prop)
    (i : I) (r r' : Raw) (h : E i r r') :
    (familyJoinLens E).equivR r r' :=
  (familyJoinLens_kernel E r r').mpr (FamilyJoinEquiv.ofI i h)

end E213.Lens.Lattice.FamilyJoin
