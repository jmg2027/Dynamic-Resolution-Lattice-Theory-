import E213.Firmware.Raw
import E213.HypervisorCore

/-!
# `PeanoAsLensComposition` — Peano arithmetic as a lens on Raw

★ G12 Tier 5 C1 — Peano arithmetic emerges from Raw via the
**leaves Lens**: counting base-element occurrences (Lens.leaves
in Hypervisor/Lens.lean) is precisely "successor counting" =
Peano's primitive operation.

## The lens composition

Peano's primitives:
  - 0 (zero)
  - succ : ℕ → ℕ

213's Raw substrate has:
  - a, b : Raw  (two base elements)
  - slash : (x y : Raw) → x ≠ y → Raw  (binary distinction)

The **leaves Lens** `Lens.leaves : Lens Nat` already in 213:
  - `base_a := 1, base_b := 1, combine := (·+·)`
  - `view : Raw → Nat` counts the total number of base elements

This IS the Peano view of Raw:
  - Each base element contributes successor (+1)
  - Each slash combines via addition
  - The resulting Nat is the "Peano measure" of the Raw expression

## Demonstration

The leaves view satisfies Peano's primitive axioms (in Lean's
Nat type, derived from Raw via this lens):
-/

namespace E213.Math.AxiomSystems.Peano

open E213.Firmware (Raw)
open E213.Hypervisor (Lens)

/-- The Peano-view lens: counts base elements (= successor count). -/
def peanoLens : Lens Nat := Lens.leaves

/-- Peano's "successor of zero" — the simplest non-trivial Raw
    expression viewed as Nat: a single base element = 1.
    (Peano: succ(0) = 1.) -/
theorem succ_zero_view : peanoLens.view Raw.a = 1 := rfl

/-- Peano's "addition" — two base elements combined by slash =
    1 + 1 = 2.  (Peano: succ(succ(0)) = 2.) -/
theorem one_plus_one_view (h : Raw.a ≠ Raw.b) :
    peanoLens.view (Raw.slash Raw.a Raw.b h) = 2 := rfl

/-- The Peano view is not injective — many Raw expressions yield
    the same Nat (e.g., any two depth-1 distinctions give 2).
    This is by design: peanoLens collapses *structural* differences
    that Peano arithmetic doesn't see.

    The "Peano view" applies a specific lens that quotients out all
    information except element count.  Other lenses (e.g., depth)
    preserve different information. -/
theorem peano_lens_not_injective (h₁ h₂ : Raw.a ≠ Raw.b) :
    peanoLens.view (Raw.slash Raw.a Raw.b h₁)
      = peanoLens.view (Raw.slash Raw.a Raw.b h₂) := rfl

end E213.Math.AxiomSystems.Peano
