import E213.Lens.Cardinality.Cantor

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
are Lens-outputs from Raw through progressively higher-order
Lens-like constructions.  Raw itself remains the same finite-
axiom-generated type throughout.

Lean 4 core can express layers explicitly up to a reasonable
depth.  Three layers here are enough to exhibit the
phenomenon for mathematicians.
-/

namespace E213.Lens.Cardinality

open E213.Theory

/-- Layer-1 abbreviation: `L1 = Raw → Bool`. -/
abbrev L1 : Type := Raw → Bool

/-- Layer-2 abbreviation: `L2 = L1 → Bool`. -/
abbrev L2 : Type := L1 → Bool

/-- ★ **Generic recursion**: the Cantor tower is unbounded.
    For every `X : Type`, the function space `X → Bool` has no
    surjection from `X`.  Since each layer `L(k+1) = L(k) → Bool`,
    every rung of the ladder is strictly higher than the previous
    one — by ONE structural statement, not layer-by-layer.

    The first two abbreviations above (`L1`, `L2`) are kept for
    callers that want concrete-layer types.  Individual rungs
    `tower_0_1`, `tower_1_2`, ... are NOT needed: applying
    `tower_unbounded` at the relevant layer type gives them
    immediately. -/
theorem tower_unbounded {X : Type} :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f :=
  cantor_general

end E213.Lens.Cardinality
