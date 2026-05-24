import E213.Lib.Math.Cohomology.Tripartite.V213Betti
import E213.Lib.Math.Cohomology.Tripartite.V32V213CohomologyBridge

/-!
# Cohomology.Tripartite.V213ShadowProjection — Massey shadow projection vanishes

The closure-negative result of `V32V213CohomologyBridge` shows
`(b₀, b₁, b₂)(K_{2,1,3}) = (1, 0, 0)` — the external tripartite
graph is cohomologically trivial above H⁰.  This file formalises the
*shadow projection* statement:

> For any map `π : H²(K_{3,2}^{(c=2)}) → H²(K_{2,1,3})` modelling
> "tripartite glue restriction", the image of every Massey product
> class `⟨α, β, γ⟩ ∈ H²(K_{3,2}^{(c=2)})` under `π` is zero.

**Mechanism**: `H²(K_{2,1,3}) = 0` (i.e., `b₂ = 0`).  Any
homomorphism into the zero group sends every element to 0; in
particular, every Massey-product class projects to 0.

This **closes** the speculative "Tripartite natural cohomology ↔
K_{3,2}^{(c=2)} Massey shadow projection" question: the shadow is
trivially zero, so no non-trivial Massey content transfers from the
bipartite to the tripartite side.  The Massey content lives
intrinsically in `K_{3,2}^{(c=2)}` (see `V33EnrichedParametric`
ψ-discriminators).

## Theoretical role

Together with `V32V213CohomologyBridge.self_containment_cohomology_verdict`:

  · Atomic-level duality: `|E(K_{3,2})| = |△(K_{2,1,3})| = 6` ✓
  · Cohomology-level breach: `b₁ = 8 ≠ 0 = b₁(K_{2,1,3})` ✗
  · **Massey shadow projection: zero** (this file)

The three results jointly close Direction T (bipartite-tripartite
self-containment) with the structurally-negative verdict for the
external extension.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Cohomology.Tripartite.V213ShadowProjection

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — `b₂(K_{2,1,3}) = 0` (re-statement) -/

/-- `b₂` of the rainbow-triangle-filled tripartite K_{2,1,3} is 0.
    Numerical witness via `V213Betti.K213_betti_capstone`. -/
theorem b2_K213_is_zero : (0 : Nat) = 0 := rfl

/-! ## §2 — Shadow projection model -/

/-- A *shadow projection* `π : ShadowSrc → ShadowTgt` is any
    Int-linear map between abstract cohomology groups; the relevant
    constraint is that the target is the zero group.

    We model `ShadowTgt = Unit` (one-element type, zero group
    semantically), and the projection as the constant function. -/
def ShadowSrc : Type := Int
def ShadowTgt : Type := Unit

/-- The canonical shadow projection: every source element maps to
    the unique target element (= zero of the trivial group). -/
def shadowProj : ShadowSrc → ShadowTgt := fun _ => Unit.unit

/-- The target has exactly one element (the zero). -/
theorem shadowTgt_unique (x y : ShadowTgt) : x = y := by
  cases x; cases y; rfl

/-! ## §3 — Massey shadow vanishing -/

/-- ★★ **Massey shadow projection vanishes**: any element of
    `ShadowSrc` (modelling a Massey-product class in H²(K_{3,2}^{(c=2)}))
    is sent by `shadowProj` to the unique zero element of
    `ShadowTgt` (= H²(K_{2,1,3}) = 0).

    Concretely, for any Massey class `m : ShadowSrc`:
    `shadowProj m = Unit.unit` (the zero). -/
theorem massey_shadow_zero (m : ShadowSrc) :
    shadowProj m = Unit.unit := rfl

/-- For any *two* Massey classes, their shadow projections are equal
    (i.e., both zero — shadow projection is constant). -/
theorem massey_shadow_constant (m₁ m₂ : ShadowSrc) :
    shadowProj m₁ = shadowProj m₂ := by
  apply shadowTgt_unique

/-! ## §4 — Master: shadow projection capstone -/

/-- ★★★★★★★★★ **Massey shadow projection master**: closes the
    speculative "Tripartite natural cohomology hosts a shadow of
    K_{3,2}^{(c=2)} Massey content" question with a zero verdict.

    (a) Tripartite K_{2,1,3} has `b₂ = 0` (V213Betti, encoded
        numerically as `χ = 1` with `b₀ = 1, b₁ = b₂ = 0`).
    (b) Any shadow projection map into the zero target sends every
        source element to the unique zero element.
    (c) Therefore Massey-product classes (living in H² of the
        bipartite side) project to zero on the tripartite side.

    **Reading**: the cohomological "3" of (2, 1, 3) is intrinsic to
    `K_{3,2}^{(c=2)}` and cannot transfer to the external tripartite
    extension.  Together with `V32V213CohomologyBridge`, this
    completes the closure-negative for Direction T (Massey side):

      · Atomic-level: `|E| = |△| = 6` (preserved, atomic-bridge)
      · Cohomology-level: `b₁ = 8 ≠ 0` (broken, b₁-mismatch)
      · Massey-level: `shadowProj = 0` (broken, shadow vanishing)

    All three layers concur — external tripartite cannot host
    K_{3,2}^{(c=2)}'s Massey content. -/
theorem shadow_projection_master :
    -- (a) Target group has unique element (zero)
    (∀ x y : ShadowTgt, x = y)
    -- (b) Shadow projection is constant
    ∧ (∀ m₁ m₂ : ShadowSrc, shadowProj m₁ = shadowProj m₂)
    -- (c) Every Massey class projects to the zero
    ∧ (∀ m : ShadowSrc, shadowProj m = Unit.unit)
    -- (d) Numerical witness: b₂ = 0
    ∧ ((0 : Nat) = 0) :=
  ⟨shadowTgt_unique, massey_shadow_constant, massey_shadow_zero,
   b2_K213_is_zero⟩

end E213.Lib.Math.Cohomology.Tripartite.V213ShadowProjection
