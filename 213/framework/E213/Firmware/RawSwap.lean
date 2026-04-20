import E213.Firmware.Raw

/-!
# Firmware: swap bijectivity (public API only)

Derives bijectivity of `Raw.swap` and the `{id, swap}` group
structure from the public `Raw.swap_swap` involution theorem
(proved in `Firmware/Raw.lean`).  This file uses only the
public `Raw.*` API — no `Tree` internals.
-/

namespace E213.Firmware

-- ═══ Thm 3.3 — swap bijectivity ═══

theorem Raw.swap_injective : Function.Injective Raw.swap := by
  intro x y h
  have := congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at this
  exact this

theorem Raw.swap_surjective : Function.Surjective Raw.swap :=
  fun y => ⟨Raw.swap y, Raw.swap_swap y⟩

theorem Raw.swap_bijective : Function.Bijective Raw.swap :=
  ⟨Raw.swap_injective, Raw.swap_surjective⟩

-- ═══ Thm 3.5 — ℤ/2 structure on {id, swap} ═══

/-- `swap ∘ swap = id`: the subgroup `{id, swap}` of the bijection
    monoid of `Raw` is isomorphic to `ℤ/2` (via order-2 element). -/
theorem Raw.swap_comp_swap : Raw.swap ∘ Raw.swap = id := by
  funext r
  exact Raw.swap_swap r

/-- `swap` is not the identity: `swap Raw.a = Raw.b ≠ Raw.a`. -/
theorem Raw.swap_ne_id : Raw.swap ≠ id := by
  intro h
  have : Raw.swap Raw.a = id Raw.a := by rw [h]
  simp [Raw.swap_a] at this
  exact absurd this (by decide)

end E213.Firmware
