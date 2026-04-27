import E213.Research.UniversalQuotLens

/-!
# Research.FamilyJoin: arbitrary-index family 의 slash-congruence
join

`FamilyMeet` 의 dual: arbitrary-index family `⟨E_i⟩_{i ∈ I}` 의
*가장 작은* slash-congruence containing all `E_i`.

## 구성

`FamilyJoinEquiv E` 가 inductive Prop 으 로 family elements +
equivalence-closure + slash-closure 의 generated relation.
`universalLens` 로 single Lens kernel realize.

## 의의

`LensMeet` (binary meet), `JoinEquiv` (binary join), `FamilyMeet`
(arbitrary meet) 와 함께 complete-lattice 구조 의 형식 화 완결:
slash-congruences 의 set 이 *complete lattice*.
-/

namespace E213.Research.FamilyJoin

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- Index 별 family 의 join: smallest slash-congruence
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

end E213.Research.FamilyJoin

namespace E213.Research.FamilyJoin

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- **Family join via universalLens**: arbitrary family
    의 join 이 single Lens 의 kernel 로 표현.  FamilyJoinEquiv
    가 inductive 로 4 closure properties 자체 carry, 따라서
    universalLens 의 hypothesis 만족. -/
def familyJoinLens {I : Type} (E : I → Raw → Raw → Prop) :
    Lens (Raw → Prop) :=
  universalLens (FamilyJoinEquiv E)

theorem familyJoinLens_kernel {I : Type} (E : I → Raw → Raw → Prop)
    (r r' : Raw) :
    (familyJoinLens E).view r = (familyJoinLens E).view r'
      ↔ FamilyJoinEquiv E r r' :=
  universalLens_kernel_eq_E (FamilyJoinEquiv E)
    FamilyJoinEquiv.refl
    (fun _ _ h => FamilyJoinEquiv.symm h)
    (fun _ _ _ h1 h2 => FamilyJoinEquiv.trans h1 h2)
    (fun _ _ _ _ h h' h1 h2 => FamilyJoinEquiv.slash_cong h h' h1 h2)
    r r'

/-- **Universal property**: 각 E_i 가 family join 안 contain. -/
theorem familyJoin_contains {I : Type} (E : I → Raw → Raw → Prop)
    (i : I) (r r' : Raw) (h : E i r r') :
    (familyJoinLens E).view r = (familyJoinLens E).view r' :=
  (familyJoinLens_kernel E r r').mpr (FamilyJoinEquiv.ofI i h)

end E213.Research.FamilyJoin
