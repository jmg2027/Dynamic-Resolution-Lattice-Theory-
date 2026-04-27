import E213.Research.FoldStructured
import E213.Research.RawACharLens

/-!
# Research.SlashCharNotFold: 특정 slash 의 characteristic 은 not fold-structured

**대응**: leaf characteristic 은 Lens-expressible (RawACharLens.lean) 지만
**specific slash 의 characteristic 은 NOT**.

## Witness

`slashAB := slash Raw.a Raw.b`.  `f r := decide (r = slashAB)`.

- f(Raw.a) = false, f(Raw.b) = false, f(slashAB) = true.
- fold structure 가정 시 c(false, false) = true (slashAB 경우).
- 그러나 slash(Raw.a, slash(Raw.a, slashAB)): 모든 sub 의 f = false,
  전체 f = false.  c(false, false) 값이 false 여야 함.
- 같은 c(false, false) 이 true 이자 false 일 수 없음.  모순.

## 의의

**Raw 의 leaf 와 non-leaf 비대칭**: leaf (Raw.a, Raw.b) 는 개별
식별 가능하지만, 특정 slash 는 view 수준에서 식별 불가능 —
slash 는 "compositional" 이어서 view 만으로는 자기 자신 구별
못 함.

이는 "관측" 개념의 정확한 한계: Raw.slash x y h 라는 **특정
구조물** 은 "위에서 내려다보는" Lens 로는 구별 안 됨.
Lens 는 fold-compositional observation 만 허용.
-/

namespace E213.Research.SlashCharNotFold

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured

/-- slashAB = slash(Raw.a, Raw.b). -/
def slashAB : Raw := Raw.slash Raw.a Raw.b (by decide)

/-- slash(a, slash(a, slashAB)). -/
def outerR : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a slashAB (by decide)) (by decide)

/-- f r := decide (r = slashAB). -/
def slashCharFn (r : Raw) : Bool := decide (r = slashAB)

end E213.Research.SlashCharNotFold

namespace E213.Research.SlashCharNotFold

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured

private theorem slashCharFn_a : slashCharFn Raw.a = false := by decide
private theorem slashCharFn_b : slashCharFn Raw.b = false := by decide
private theorem slashCharFn_slashAB : slashCharFn slashAB = true := by decide
private theorem slashCharFn_outerR : slashCharFn outerR = false := by decide

-- slash(a, slashAB) 의 f = false (≠ slashAB since structure 다름).
private def innerR : Raw := Raw.slash Raw.a slashAB (by decide)
private theorem slashCharFn_innerR : slashCharFn innerR = false := by decide

/-- **slashCharFn 은 fold-structured 아님**. -/
theorem slashCharFn_not_fold_structured :
    ¬ FoldStructured slashCharFn := by
  intro ⟨ba, bb, c, hba, hbb, _, hslash⟩
  -- slashAB = slash(a, b, _).  f(slashAB) = c(f a)(f b) = c(ba)(bb)
  --                                        = c(false)(false) (after hba, hbb)
  -- f(slashAB) = true ⟹ c(false, false) = true.
  have h1 : slashCharFn slashAB
              = c (slashCharFn Raw.a) (slashCharFn Raw.b) :=
    hslash Raw.a Raw.b (by decide)
  rw [slashCharFn_slashAB, slashCharFn_a, slashCharFn_b] at h1
  -- h1 : true = c false false
  -- outerR = slash(a, innerR, _).  f(outerR) = c(f a)(f innerR) = c(false, false)
  -- f(outerR) = false ⟹ c(false, false) = false.
  have h2 : slashCharFn outerR
              = c (slashCharFn Raw.a) (slashCharFn innerR) :=
    hslash Raw.a innerR (by decide)
  rw [slashCharFn_outerR, slashCharFn_a, slashCharFn_innerR] at h2
  -- h2 : false = c false false
  -- h1, h2: c(false, false) = true and false. Contradiction.
  rw [← h1] at h2
  exact absurd h2 (by decide)

end E213.Research.SlashCharNotFold
