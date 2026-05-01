import E213.Firmware.Raw.SwapSlash
import E213.Prelude

/-!
# Research.SwapSlash: Function.Injective / Surjective form of Raw.swap

The key theorems `Raw.swap_injective` and `Raw.swap_slash` are in Firmware
(`Firmware/Raw/Swap.lean`, `Firmware/Raw/SwapSlash.lean`).

This file restates them in the `Function.Injective` / `Function.Surjective`
form (for use within the Lens framework).
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
