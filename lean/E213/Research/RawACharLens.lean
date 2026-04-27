import E213.Hypervisor.Lens
import E213.Research.LensFactoring
import E213.Research.LeafLens

/-!
# Research.RawACharLens: Raw.a 의 characteristic function 은 Lens

**관찰**: `fun r => decide (r = Raw.a)` 는 fold-structured 함수
(따라서 Lens 로 실현 가능).

combine = const false 로 구현.

## 이유 (왜 leaf 만 가능한가)

- Raw.a 는 leaf.  "s = Raw.a" 는 base 분기에서만 결정됨.
  slash 분기는 자동으로 false (slash ≠ leaf).
- Raw.slash x y h 같은 특정 slash r 에 대해서는 "s = r" 이
  fold-structured 아님 — s = r 여부가 view x, view y 만으로
  결정되지 않음 (subtree 구조 직접 봐야 함).

**Leaf 는 Lens 로 관측 가능, 특정 slash 는 관측 불가능**.

## 새 kernel class

2-class partition: {Raw.a} vs {모든 나머지}.  기존 카탈로그의
leafLens ({leaves} vs {slashes}) 와 다름.
-/

namespace E213.Research.RawACharLens

open E213.Firmware E213.Hypervisor

/-- Raw.a 의 characteristic Lens. -/
def rawACharLens : Lens Bool where
  base_a := true
  base_b := false
  combine _ _ := false

theorem rawACharLens_view_eq :
    ∀ r : Raw, rawACharLens.view r = decide (r = Raw.a) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : rawACharLens.view (Raw.slash x y h)
                   = rawACharLens.combine
                       (rawACharLens.view x) (rawACharLens.view y) := by
        apply Raw.fold_slash
        intro _ _; rfl
      rw [hfs]
      show (false : Bool) = decide (Raw.slash x y h = Raw.a)
      have hne : Raw.slash x y h ≠ Raw.a := by
        intro heq
        have hv : (Raw.slash x y h).val = Raw.a.val :=
          congrArg Subtype.val heq
        have hra : Raw.a.val = (.a : E213.Firmware.Internal.Tree) := rfl
        rw [hra] at hv
        unfold Raw.slash at hv
        split at hv <;> rename_i hcmp
        · exact E213.Firmware.Internal.Tree.noConfusion hv
        · exact E213.Firmware.Internal.Tree.noConfusion hv
        · exact h (Subtype.ext
            ((E213.Firmware.Internal.Tree.cmp_eq_iff _ _).mp hcmp))
      rw [decide_eq_false hne]

end E213.Research.RawACharLens

namespace E213.Research.RawACharLens

open E213.Firmware E213.Hypervisor E213.Research.LeafLens

/-- Raw.a vs Raw.b: leafLens 는 equate, rawACharLens 는 구별. -/
theorem leafLens_equates_a_b :
    leafLens.view Raw.a = leafLens.view Raw.b := rfl

theorem rawACharLens_distinguishes_a_b :
    rawACharLens.view Raw.a ≠ rawACharLens.view Raw.b := by decide

theorem leafLens_not_refines_rawACharLens :
    ¬ leafLens.refines rawACharLens := by
  intro h
  exact rawACharLens_distinguishes_a_b
    (h Raw.a Raw.b leafLens_equates_a_b)

/-- rawACharLens 는 leafLens 를 refine 하지 않음.
    Witness: Raw.b (not-a-leaf? no, leaf) vs slash(a, b).
    둘 다 "≠ Raw.a" 이지만 leafLens 는 구별 (leaf vs slash). -/
theorem rawACharLens_not_refines_leafLens :
    ¬ rawACharLens.refines leafLens := by
  intro h
  let sab := Raw.slash Raw.a Raw.b (by decide)
  have hrawa_eq : rawACharLens.view Raw.b = rawACharLens.view sab := by decide
  have : leafLens.view Raw.b = leafLens.view sab := h _ _ hrawa_eq
  exact absurd this (by decide)

end E213.Research.RawACharLens
