import E213.Hypervisor.Lens
import E213.Research.RawInitiality

/-!
# Research.FoldStructured: Lens-expressible 함수의 정확한 특성화

**주장**: f : Raw → α 가 어떤 Lens 의 view 이다 ↔ f 가
**fold-structured** (base 값 + symmetric combine 으로 recurrence
만족).

## 의의

이 arc 전체의 중심 결과.  "어떤 Raw → α 함수가 Lens 로
표현 가능한가?" 의 정확한 답.

Kernel 쪽에서는 `KernelCongruence.lean` 이 같은 질문의
equivalence relation 버전 (slash-congruence ↔ Lens kernel).
이 파일은 **함수 버전**.
-/

namespace E213.Research.FoldStructured

open E213.Firmware E213.Hypervisor E213.Research.RawInitiality

/-- `f : Raw → α` 이 fold-structured. -/
def FoldStructured {α : Type} (f : Raw → α) : Prop :=
  ∃ (ba bb : α) (c : α → α → α),
    (f Raw.a = ba) ∧ (f Raw.b = bb) ∧
    (∀ u v, c u v = c v u) ∧
    (∀ (x y : Raw) (h : x ≠ y), f (Raw.slash x y h) = c (f x) (f y))

/-- **Forward**: Lens view 는 fold-structured. -/
theorem lens_view_fold_structured {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u) :
    FoldStructured L.view := by
  refine ⟨L.base_a, L.base_b, L.combine, rfl, rfl, hsym, ?_⟩
  intro x y h
  exact Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

/-- **Backward**: fold-structured 함수는 Lens view 로 realize 됨. -/
theorem fold_structured_lens_expressible {α : Type} (f : Raw → α)
    (hfold : FoldStructured f) :
    ∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧ L.view = f := by
  obtain ⟨ba, bb, c, hba, hbb, hsym, hslash⟩ := hfold
  refine ⟨⟨ba, bb, c⟩, hsym, ?_⟩
  funext r
  have := Lens.view_unique (α := α) ⟨ba, bb, c⟩ hsym f hba hbb hslash r
  exact this.symm

end E213.Research.FoldStructured

namespace E213.Research.FoldStructured

open E213.Firmware E213.Hypervisor

/-- **Main theorem (iff)**: f 가 어떤 symmetric-combine Lens 의
    view 이다 ↔ f 가 fold-structured. -/
theorem lens_expressible_iff_fold_structured {α : Type} (f : Raw → α) :
    (∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧ L.view = f)
      ↔ FoldStructured f := by
  constructor
  · intro ⟨L, hsym, hview⟩
    rw [← hview]
    exact lens_view_fold_structured L hsym
  · exact fold_structured_lens_expressible f

end E213.Research.FoldStructured
