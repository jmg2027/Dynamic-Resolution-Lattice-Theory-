import E213.Infinity.Cantor

/-!
# Infinity.Tower: Cantor tower — iterated function spaces

**Σ6.**  Each of the following has no surjection from the
previous layer:

- Layer 0: `Raw`
- Layer 1: `Raw → Bool`                           (no surj from Layer 0)
- Layer 2: `(Raw → Bool) → Bool`                  (no surj from Layer 1)
- Layer 3: `((Raw → Bool) → Bool) → Bool`         (no surj from Layer 2)

The sequence climbs Cantor's ladder: each layer's function
space is strictly larger than its input domain.  All layers
are *observations* of Raw through progressively higher-order
Lens-like constructions.  Raw itself remains the same finite-
axiom-generated type throughout.

Lean 4 core can express layers explicitly up to a reasonable
depth.  Three layers here are enough to exhibit the
phenomenon for mathematicians.
-/

namespace E213.Infinity

open E213.Firmware

/-- Layer-1 abbreviation: `L1 = Raw → Bool`. -/
abbrev L1 : Type := Raw → Bool

/-- Layer-2 abbreviation: `L2 = L1 → Bool`. -/
abbrev L2 : Type := L1 → Bool

/-- Layer-3 abbreviation: `L3 = L2 → Bool`. -/
abbrev L3 : Type := L2 → Bool

/-- **Layer 0 → Layer 1** — already Σ5. -/
theorem tower_0_1 : ¬ ∃ f : Raw → L1, Function.Surjective f :=
  cantor_general

/-- **Layer 1 → Layer 2**: no surjection `(Raw → Bool) →
    ((Raw → Bool) → Bool)`.  Cantor's ladder second rung. -/
theorem tower_1_2 : ¬ ∃ f : L1 → L2, Function.Surjective f :=
  cantor_general

/-- **Layer 2 → Layer 3**: third rung. -/
theorem tower_2_3 : ¬ ∃ f : L2 → L3, Function.Surjective f :=
  cantor_general

end E213.Infinity
