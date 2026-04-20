import E213.Clean213

/-!
# Swap automorphism on Raw

The firmware (Clean213) has two base constants `a, b` and the
`slash` constructor. The swap operation exchanges the two base
constants and extends recursively.

This gives `Aut(Raw) ≅ ℤ/2`:
- identity
- swap (exchange a ↔ b at every leaf)

No equality primitive is used in the definition of `swap`; it is
defined by structural recursion on the Raw constructors.
-/

/-- Swap: exchange the two base somethings; extend to `slash`
    recursively. -/
def Raw.swap : Raw → Raw
  | .a         => .b
  | .b         => .a
  | .slash x y => .slash (Raw.swap x) (Raw.swap y)

/-- Swap is involutive. -/
theorem Raw.swap_swap : ∀ x : Raw, Raw.swap (Raw.swap x) = x
  | .a         => rfl
  | .b         => rfl
  | .slash x y => by
      simp [Raw.swap, Raw.swap_swap x, Raw.swap_swap y]

/-- Involutive ⟹ injective. -/
theorem Raw.swap_injective {x y : Raw}
    (h : Raw.swap x = Raw.swap y) : x = y := by
  have := congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at this
  exact this

/-- A Lens is swap-invariant if its view agrees on `x` and `swap x`. -/
def Lens.SwapInvariant {α : Type} (L : Lens α) : Prop :=
  ∀ x : Raw, L.view (Raw.swap x) = L.view x

/-- **Swap-invariance forces the two base values to coincide.**
    At the Lens layer, a swap-invariant Lens cannot distinguish
    the two base somethings. -/
theorem Lens.swapInvariant_base_eq {α : Type} {L : Lens α}
    (h : L.SwapInvariant) : L.base_a = L.base_b := by
  have h0 := h .a
  simp [Lens.view, Raw.swap] at h0
  exact h0.symm
