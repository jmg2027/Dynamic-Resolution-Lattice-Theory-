# Lens Number Systems

**Status**: Closed (25 files; Nat213 sub-tree covered in universe_chain;
founding sub-tree under `Founding` umbrella).

## Overview

**Raw-derived number systems**: each module is a `Raw.fold`
catamorphism output reified as a number system.  Per
`lean/E213/ARCHITECTURE.md`: **catamorphism + data choice =
Lens-layer artifact**.

## Lean source

- `lean/E213/Lens/Number/` (25 files including `Nat213/` sub-tree)
- Founding umbrella: `lean/E213/Lens/Number/Founding.lean`
- ∅-axiom PURE (`tools/scan_axioms.py` → 0 DIRTY across the sub-tree)

## Narrative

Different `Raw.fold` choices yield different number systems:
- **Nat213** (`Nat213/`) = (NS-spatial + NT-temporal) constructor counts → ℕ-like
- **Int213** = signed extension via SignedCut-style pair
- **Other Lens.Number** instances: rational, dyadic, ...

`Nat213/` sub-tree is **fully covered** in
`theory/math/foundations/universe_chain.md` — atomicity → Möbius → CRT chapter.
This Lens-side chapter is for the **classification frame**: number
systems as Lens-layer artifacts, not Theory-layer foundations.

## Founding sub-tree (`Founding` umbrella)

The tower `ℕ → ℤ → ℚ → ℝ` is founded rung-by-rung as a chain of Lens
bundlings, with its closure properties.  Key results:

| Theorem | Module | Statement (informal) |
|---|---|---|
| `number_tower_is_lens_bundling` | `TowerFounding` | the four rungs chain: count (`+`), difference (`ℤ`, count-Lens bundled into a group), ratio (`ℚ`, lowest-terms = `det P = NS − NT`), Cauchy completion (`ℝ`, the fixpoint) |
| `invert_is_one_move` | `Nat213/Tower/PairCompletion` | `ℤ` and `ℚ_+` are one generic `CommCancelSemigroup` pair-completion at `+` and `·`; the group identity emerges as the diagonal, unit-free |
| `swap_order_eq_NT` | `Nat213/Tower/PairCompletion` | the inverse-realising swap has order exactly `NT = 2` — period-2 forced by the count, no period-`k` on a pair |
| `mul_self_inj` | `Nat213/Order` | native strict order (Lean `Nat` order is propext-dirty): trichotomy + strict square-monotonicity (from distributivity) → `a·a = b·b → a = b` |
| `reciprocal_fixed_iff_unit` | `Nat213/Tower/NatPairToQPos` | the reciprocal involution, full twin of `ℤ`'s `zero_unique_negation_fixed` |
| `the_unit_is_one_across_readings` | `SharedUnitAcrossReadings` | the unit `1` is one value across count-difference, Möbius/ratio determinant, Cassini oscillation, and reciprocal — identity-of-the-unit, the honest axis-unification |

The standalone treatise reading these as one structure — complete at `ℝ`
(fixpoint), hybrid as axes (one unit, many readings), forced only at its
seams — is `book/foundations/`.

## Connection

- `book/foundations/` — the standalone founding treatise (the three
  questions: complete tower? one axis? forced?)
- `theory/math/foundations/universe_chain.md` — Nat213 sub-tree narrative
- `lean/E213/ARCHITECTURE.md` — catamorphism = Lens artifact
- `theory/lens/algebra.md` — kernel underlies catamorphism choice
