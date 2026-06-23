# Simplex Δ⁴ + 3-Generation Structure

**Status**: Closed (7 files).

## Overview

**Δ⁴ simplex enumeration** + the **3-generation structure** of
fermions.  Δ⁴ has C(5, k) sub-faces at each dimension; the
3-generation count emerges as the structural reading of the
sub-face inventory.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Simplex/` (7 files)
- **Umbrella**: `Simplex.lean`
- **∅-axiom status**: PURE

## Narrative

Δ⁴ (the 4-simplex on 5 vertices) has sub-face counts:
- dim 0: C(5,1) = 5 vertices
- dim 1: C(5,2) = 10 edges
- dim 2: C(5,3) = 10 triangles
- dim 3: C(5,4) = 5 tetrahedra
- dim 4: C(5,5) = 1 4-simplex

Total non-empty sub-simplices = `2^5 − 1 = 31` (Mersenne).

The **3-generation** structure (3 fermion families in the Standard
Model) emerges as `N_gen = C(NS, NT) = C(3, 2) = 3` — the binomial
count derived in `Lib/Physics/Simplex/Generations.lean`
(`drlt_no_4th_gen_falsifier`).  Each generation = one of the three.

`SubInventory.lean` enumerates the sub-simplex counts; `FaceTerms.lean`
provides the face-by-face cup-product breakdown used in α_em
precision chapter.

**N_gen = 3** is one of the canonical DRLT falsifiers (per
`seed/AXIOM/08_falsifiability.md`): discovery of a 4th generation
would falsify.

## Connection

- `theory/physics/foundations/atomic_constants.md` — d = 5 = |Δ⁴ vertices|
- `theory/physics/alpha_em/precision_derivation.md` — FaceTerms used
- `catalogs/falsifiers.md` — N_gen = 3 entry
