# Refined completability engine — completability as an intensional ordinal grade

**Status**: Closed.  Source of truth (all ∅-axiom): `lean/E213/Lib/Math/Real213/{CompletabilityGrade,
IntensionalCompletability, RefinedCompletabilityEngine, HeightTowerResidue}`.

## Overview

`tower_native_completeness.md` reduced "which reals complete?" to a comparison of two
growth-axes (cross-determinant `W` vs denominator `d`), with a *binary* boundary
(`CrossDetSmall` holds or fails) sorted into rungs by the discriminant sign.  The
sign is one bit — the coarsest shadow.  This chapter refines the binary boundary into a
two-axis **engine** that lives entirely inside the reals:

  * an **ordinal height** axis — completability is graded `ω·height + rate`, with the
    height ranging over the whole exponential tower and the rate the finite part within a
    height;
  * an **intensional gauge** axis — the sufficient *test* is presentation-relative
    (canonical on the reduced presentation) while the *truth* (the cut's completion) is
    gauge-invariant.

Read together: a real's completability is the lex ordinal `(height, rate)` of its
gcd-reduced presentation — an intensional invariant of the cut, neither a yes/no fact
nor the bare cut.  The height tower runs from the det-one floor with no top; its ceiling
is the residue.

## Lean source

| File | PURE / dirty | Content |
|---|---|---|
| `Real213/CompletabilityGrade.lean` | 7 / 0 | the lex `(height, rate)` grade; height an `ω`-coordinate over the exponential tower |
| `Real213/IntensionalCompletability.lean` | 3 / 0 | the test antitone under rescaling (reduced canonical); completion gauge-invariant |
| `Real213/RefinedCompletabilityEngine.lean` | 1 / 0 | both axes bundled as one engine |
| `Real213/HeightTowerResidue.lean` | 2 / 0 | the height tower has no top; its diagonal is the residue |

Builds under the `E213.Lib.Math.Real213` umbrella.

## Narrative

### The height axis is an ordinal, height dominating rate

Within one exponential height — a geometric cross-determinant `W_i = r^i` over a
geometric denominator `d_i = q^i` — completability is decided by the **rate**, free iff
`r < q` (`GeometricThreshold.geom_boundary_iff`).  But the rate is not the whole story.
Crossing one exponential layer **up** breaks the bridge regardless of rate:

  * `height_two_overtakes` — a double-exponential `W_i = q^{b^i}` over a single-exponential
    `d_i = q^i` breaks `CrossDetSmall` for *any* bases `q, b ≥ 2` (tested at `i = 2`:
    `q^3 ≤ q^{b^2}`, feeding `overtake_breaks_at`);
  * `height_one_under_height_two` — going *down* an exponential height is always free
    (the double-exponential denominator swamps the single-exponential cross-determinant).

So completability is governed by the lexicographic order `(height, rate)` — the ordinal
`ω·height + rate`, with the exponential height the dominant (`ω`) coordinate and the
geometric rate the finite refinement (`completability_grade`).  The height is a *genuine*
`ω`-coordinate, not just `{1, 2}`: `expTower_succ_le` (one index step costs less than one
exponential layer) gives `height_succ_overtakes` — *every* step up the exponential tower
`DepthOmegaTower.expTower` breaks `CrossDetSmall` — so `height_is_omega_coordinate`:
`∀ r`, the height-`(r+2)` tower overtakes the height-`(r+1)` denominator.

### The intensional gauge axis

The cross-determinant bridge reads the **representation**, not the bare real.  A cut has a
whole rescaling orbit of presentations `(a, d) ↦ (c·a, c·d)`, and the two come apart along
it:

  * `crossdet_rescale_antitone` — `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` for
    `c ≥ 1`: the cross-determinant scales `c²` against a denominator scaling `c`, so
    rescaling *up* only loses the bridge.  The **gcd-reduced** presentation is the
    canonical (easiest) place to test `CrossDetSmall` — the test is antitone down the
    rescaling order;
  * `modulus_rescale_invariant` — a total modulus for `a/d` is *the same* for `(c·a)/(c·d)`
    (the cut cancels the common factor, `PresentationDependence.rcut_rescale`).  Completion
    is a fact about the cut, not the presentation.

`completability_is_intensional` bundles them: the sufficient **test** is
presentation-relative, the **truth** it certifies is presentation-invariant.  The
intensional content is the gauge class; the cut is its collapse; the canonical ordinal
grade is read on the reduced representative.

### The engine, and its `ε₀` ceiling

`refined_completability_engine` bundles the four facts — ordinal grade, height as an
`ω`-coordinate, test antitone, truth gauge-invariant — into one statement: a real's
completability is the lex ordinal `(height, rate)` of its gcd-reduced presentation.

The height tower runs from the det-one **floor** (`DepthFloorDetOne`, the trivially-free
bottom) with **no top**.  `height_tower_no_top`: the diagonal `diag (expTower q) n =
expTower q n n + 1` is not any level `expTower q r` — naming the whole tower produces a
growth outside every finite height.  `height_tower_residue` bundles the open-endedness
with its meaning: every step up overtakes (no final level), the diagonal escapes every
level (no top), and that diagonalization **is** the pointing/Cantor residue
(`DepthCeilingResidue.ceiling_reference_leaves_residue`).  So the floor (bottom) and the
residue (top) close into one self-cover loop: the refined real engine has no exterior, and
the height tower's ceiling is the residue read at the scale of divergence-complexity.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `completability_grade` | `CompletabilityGrade` | lex `(height, rate)`: down free, within free ⟺ `r<q`, up broken |
| `height_is_omega_coordinate` | `CompletabilityGrade` | every exponential-tower step up breaks `CrossDetSmall` |
| `crossdet_rescale_antitone` | `IntensionalCompletability` | rescaling up only loses the bridge (reduced canonical) |
| `modulus_rescale_invariant` | `IntensionalCompletability` | completion is gauge-invariant (cut's truth) |
| `refined_completability_engine` | `RefinedCompletabilityEngine` | both axes as one engine |
| `height_tower_no_top` | `HeightTowerResidue` | the height tower's diagonal escapes every level |
| `height_tower_residue` | `HeightTowerResidue` | no top; the diagonalization is the residue |

## Open frontier

- **Within-height rate beyond height 1.**  The rate refinement is closed at height 1
  (`r < q`); the fine structure inside higher tower levels is not yet a theorem.
- **Continued-fraction universality.**  Every irrational's continued-fraction convergents
  sit on the det-one floor (`W = ±1`) and are rate-carrying; promoting that to an
  ∅-axiom "universal rate-carrying chart" would make the floor (and so the whole engine)
  universal over the reals.
- **Honest scope.**  What is proven: the lex structure, height as an `ω`-coordinate, the
  test's antitonicity, the truth's gauge-invariance, and that the tower has no top (the
  diagonal escapes = Cantor self-cover).  The `ε₀`/Veblen ordinal names are the classical
  reading of these diagonalisation facts, not a formalised ordinal arithmetic.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Real213
cd ..
for M in \
  E213.Lib.Math.Real213.CompletabilityGrade \
  E213.Lib.Math.Real213.IntensionalCompletability \
  E213.Lib.Math.Real213.RefinedCompletabilityEngine \
  E213.Lib.Math.Real213.HeightTowerResidue ; do
    python3 tools/scan_axioms.py $M
done
```
Each module reports `N pure / 0 dirty`.
