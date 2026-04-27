import E213.Firmware.Raw.SwapSlash
import E213.Prelude

/-!
# Research.SwapSlash: Raw.swap 의 Function.Injective / Surjective form

핵심 정리 `Raw.swap_injective`, `Raw.swap_slash` 는 Firmware
(`Firmware/Raw/Swap.lean`, `Firmware/Raw/SwapSlash.lean`)
에 있음.

이 파일은 `Function.Injective` / `Function.Surjective` form
(Lens framework 내 사용) 재정리.
-/

namespace E213.Research.SwapSlash

open E213.Firmware

/-- `Function.Injective` form. -/
theorem Raw.swap_injective' : Function.Injective Raw.swap :=
  fun _ _ h => Raw.swap_injective h

/-- `Function.Surjective` form (self-inverse). -/
theorem Raw.swap_surjective : Function.Surjective Raw.swap :=
  fun y => ⟨Raw.swap y, Raw.swap_swap y⟩

end E213.Research.SwapSlash
