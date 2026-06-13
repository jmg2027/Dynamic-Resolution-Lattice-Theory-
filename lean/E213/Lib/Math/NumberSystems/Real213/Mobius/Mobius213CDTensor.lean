import E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCutMul
import E213.Meta.Tactic.NatHelper

/-!
# Mobius213CDTensor — the 5th architectural pattern

Extends the four patterns in `theory/essays/methodology/pure_funext_avoidance.md`
(State Accumulator / Bundled Subtype / Setoid Category /
Residual Induction) with a fifth: **CD-Tensor Bundling**, for
fiber-changing operations.

## The problem this pattern addresses

The four existing patterns handle within-fiber Lean obstructions
(funext-blocked equality, propext-blocked composition, carry
chains, truncation lifts).  They suffice when the operation
preserves its fiber.

**Multiplication on N-fiber cuts changes fiber to N²-fiber**.
Search-based `cutMulN N` only closes forward; the backward
direction has a precision artifact because the natural witnesses
`m1 = a · k, m2 = c · k` are unbounded in the input numerators
`a, c`.  No fixed search bound suffices.

The fifth pattern: instead of forcing a single fiber-changing
operation to close bidirectionally at the bool-search level,
**bundle the operation as a tensor structure** that retains
the source-fiber data alongside the canonical product.  The
"missing backward direction" becomes a non-question: there is
no backward search to perform, because the operation IS the
tensor construction.

## What this file delivers

  · `MobiusTensor N₁ N₂` — the tensor structure: a factor pair
    `(factor_a : ValidCutN N₁, factor_b : ValidCutN N₂)` plus
    their canonical product `product : ValidCutN (N₁ · N₂)`.
  · `fromPair` — build a tensor from a same-fiber pair.
  · Field projections (`rfl` lemmas).
  · `fromPair_commutes_at_represents` — commutativity at the
    represents level via `Nat.mul_comm`.
  · `MobiusTensor_master` — the 5th pattern realization
    theorem.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213CDTensor

open E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut (ValidCutN ofValidCutN)
open E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCutMul (mulN mulN_represents mulN_cut)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — The MobiusTensor structure -/

/-- ★★★★★ **The 5th architectural pattern**: a bundled tensor
    structure for fiber-changing multiplication.  Retains the
    two source-fiber factors alongside their canonical product
    at the doubled fiber. -/
structure MobiusTensor (N₁ N₂ : Nat) where
  /-- First factor at fiber `N₁`. -/
  factor_a : ValidCutN N₁
  /-- Second factor at fiber `N₂`. -/
  factor_b : ValidCutN N₂
  /-- The canonical product at fiber `N₁ · N₂`. -/
  product  : ValidCutN (N₁ * N₂)
  /-- Algebraic compatibility: the product's `represents` field
      is exactly the product of the factors' `represents`. -/
  product_eq : product.represents = factor_a.represents * factor_b.represents

/-! ## §2 — Constructor from a same-fiber pair -/

/-- ★★★★ Build a `MobiusTensor N N` from two `ValidCutN N`
    factors.  Uses the existing bundled `mulN` for the product
    field. -/
def fromPair {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    MobiusTensor N N where
  factor_a := a
  factor_b := c
  product := mulN N hN a c
  product_eq := mulN_represents N hN a c

theorem fromPair_factor_a {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).factor_a = a := rfl

theorem fromPair_factor_b {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).factor_b = c := rfl

theorem fromPair_product {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).product = mulN N hN a c := rfl

theorem fromPair_product_represents
    {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).product.represents = a.represents * c.represents :=
  mulN_represents N hN a c

theorem fromPair_product_cut
    {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).product.cut
      = constCut (a.represents * c.represents) (N * N) :=
  mulN_cut N hN a c

/-! ## §3 — Tensor-level commutativity (represents level) -/

/-- ★★★★ **Commutativity at the represents level**: swapping
    the factors in a tensor yields the same product numerator
    `a.r · c.r = c.r · a.r` (Nat multiplication is commutative). -/
theorem fromPair_commutes_at_represents
    {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).product.represents
      = (fromPair hN c a).product.represents := by
  rw [fromPair_product_represents, fromPair_product_represents,
      Nat.mul_comm]

/-- ★★★★ **Cut-level commutativity** of the bundled product:
    `constCut (a · c) (N · N) = constCut (c · a) (N · N)` since
    `Nat.mul_comm`. -/
theorem fromPair_commutes_at_cut
    {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    (fromPair hN a c).product.cut
      = (fromPair hN c a).product.cut := by
  rw [fromPair_product_cut, fromPair_product_cut, Nat.mul_comm a.represents]

/-! ## §4 — Associativity (3-factor tensor at represents level)

A 3-factor product `a · c · e` can be bundled as either
`(a · c) · e` or `a · (c · e)`.  At the represents level these
agree by `Nat.mul_assoc`.  At the type level, the doubled
fibers are `N⁴` vs `N · N² = N³` — these match definitionally
via `Nat.mul_assoc` on the fiber index, but Lean would need
explicit transport.  We record the represents-level identity. -/

/-- ★★★ **3-factor represents-level associativity**: the
    `represents` field is `Nat.mul_assoc`-compatible across
    tensor compositions. -/
theorem three_factor_represents_assoc
    (a b c : Nat) :
    a * b * c = a * (b * c) :=
  E213.Tactic.NatHelper.mul_assoc a b c

/-! ## §5 — 5th pattern master -/

/-- ★★★★★★ **5th architectural pattern realization**: the
    MobiusTensor structure exhibits:
    (a) factor / product fields with definitional projections
    (b) represents-level multiplicative compatibility
    (c) cut-level canonical form via constCut
    (d) commutativity at both represents and cut levels
    (e) Nat-level associativity for chained tensor products

    Together: a fiber-changing operation expressed as a
    structural tensor with all algebraic data preserved. -/
theorem MobiusTensor_master
    {N : Nat} (hN : 0 < N) (a c : ValidCutN N) :
    -- (a) Field projections by rfl
    (fromPair hN a c).factor_a = a
    ∧ (fromPair hN a c).factor_b = c
    ∧ (fromPair hN a c).product = mulN N hN a c
    -- (b) Represents-level multiplicative compatibility
    ∧ (fromPair hN a c).product.represents = a.represents * c.represents
    -- (c) Cut-level canonical form
    ∧ (fromPair hN a c).product.cut
        = constCut (a.represents * c.represents) (N * N)
    -- (d) Commutativity at both levels
    ∧ (fromPair hN a c).product.represents
        = (fromPair hN c a).product.represents
    ∧ (fromPair hN a c).product.cut
        = (fromPair hN c a).product.cut
    -- (e) Nat-level associativity (chain of 3)
    ∧ (a.represents * c.represents * c.represents
        = a.represents * (c.represents * c.represents)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · exact mulN_represents N hN a c
  · exact mulN_cut N hN a c
  · exact fromPair_commutes_at_represents hN a c
  · exact fromPair_commutes_at_cut hN a c
  · exact three_factor_represents_assoc a.represents c.represents c.represents

end E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213CDTensor
