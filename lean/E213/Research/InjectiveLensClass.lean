import E213.Hypervisor.Lens
import E213.Prelude

/-!
# Research.InjectiveLensClass: injective Lens 의 유일 equivalence class

**관찰**: Refines preorder 의 equivalence class 관점에서,
**injective 인 모든 Lens 는 한 class 에 속함**.

## 정리

`L.view`, `M.view` 둘 다 injective 이면 `L ≈ M` (서로 refine).

## 의의

Note 37 에서 `idLens` 가 bottom (모든 Lens 를 refine) 임을
확인.  이 파일은 추가: **idLens 가 injective 대표** — 모든
injective Lens 는 idLens 와 동치.

즉 injective Lens 의 "공간" 은 1점 (up to equivalence).
-/

namespace E213.Research.InjectiveLensClass

open E213.Firmware E213.Hypervisor

/-- **Injective equivalence**: 두 injective Lens 는 서로 refine. -/
theorem injective_equiv {α β : Type} (L : Lens α) (M : Lens β)
    (hL : Function.Injective L.view) (hM : Function.Injective M.view) :
    L.refines M ∧ M.refines L := by
  constructor
  · intro x y hxy
    have heq : x = y := hL hxy
    show M.view x = M.view y
    rw [heq]
  · intro x y hxy
    have heq : x = y := hM hxy
    show L.view x = L.view y
    rw [heq]

end E213.Research.InjectiveLensClass
