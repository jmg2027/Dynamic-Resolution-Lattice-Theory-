import E213.Research.UniversalQuotLens

/-!
# Research.ChoiceResolved: "선택 = Lens specification" 의 formal

Note 44 의 thesis 의 explicit formalization:

**임의 slash-congruence E 에 대해 concrete Lens 가 존재**.
Classical.choice 또는 외부 axiom 추가 없이.

이것이 213 안에서 "choice 가 Lens spec 으로 환원" 의 정확한
의미.  추상 적 choice 함수 가 아니라 universalLens 구성 으로
명시 적 Lens 지정.

## 정리

`choice_as_lens_spec`: ∀ E (equiv + slash-cong), ∃ L : Lens
  (Raw → Prop), ∀ r r', L.view r = L.view r' ↔ E r r'.

증명: ⟨universalLens E, universalLens_kernel_eq_E E ...⟩.

External axiom 0.  Constructive existence — 명시 적 witness
universalLens E.
-/

namespace E213.Research.ChoiceResolved

open E213.Firmware E213.Hypervisor E213.Research.UniversalQuotLens

/-- **Choice resolved**: 임의 slash-congruence E 에 대해 concrete
    Lens 존재 (external axiom 0).  Classical.choice 부재 하 universal
    construction. -/
theorem choice_as_lens_spec (E : Raw → Raw → Prop)
    (hrefl : ∀ r, E r r)
    (hsymm : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h')) :
    ∃ L : Lens (Raw → Prop),
      ∀ r r' : Raw, L.view r = L.view r' ↔ E r r' :=
  ⟨universalLens E,
   fun r r' => universalLens_kernel_eq_E E hrefl hsymm htrans hslash r r'⟩

/-- **Choice 가 Lens 인스턴스 의 직접 귀결**: 각 slash-cong E 에
    대해 universalLens E 가 그 choice 의 명시 witness. -/
def witness_explicit (E : Raw → Raw → Prop) :
    Lens (Raw → Prop) := universalLens E

end E213.Research.ChoiceResolved
