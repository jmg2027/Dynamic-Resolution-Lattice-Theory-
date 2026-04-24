import E213.Firmware.Raw
import E213.Prelude

/-!
# Research.SwapSlash: Raw.swap injectivity

**정리**: `Raw.swap` 은 injective (자명 — involution 이므로).

## 의의

`swap_swap` (involutivity) 의 직접 귀결.  Raw.swap 이 Raw 의
automorphism 임을 보장하는 기본 조각.

Raw.swap 이 Raw.slash 와 호환 (swap_slash) 이라는 더 강한
정리는 canonical form 의 깊은 case analysis 가 필요하여 이
파일에서는 제외 — future work.
-/

namespace E213.Research.SwapSlash

open E213.Firmware

/-- Raw.swap 은 injective (swap_swap 에서 직접 귀결). -/
theorem Raw.swap_injective :
    ∀ x y : Raw, Raw.swap x = Raw.swap y → x = y := by
  intro x y h
  have happ : Raw.swap (Raw.swap x) = Raw.swap (Raw.swap y) :=
    congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at happ
  exact happ

/-- Raw.swap 은 injective (Function.Injective form). -/
theorem Raw.swap_injective' : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective _ _ h

/-- Raw.swap 은 surjective. -/
theorem Raw.swap_surjective : Function.Surjective Raw.swap :=
  fun y => ⟨Raw.swap y, Raw.swap_swap y⟩

end E213.Research.SwapSlash
