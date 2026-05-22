# SignedCut — Sign Extension on Real213 Cuts

**Status**: Closed (35 files in 6 sub-clusters, sub-organized 2026-05-13).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 (multi-note absorption from G37-G39).  Absorbs
G37 (Level25 residual), G38 (Unified 25-level algebra),
G39 (Octonion non-assoc witness).

## Overview

**SignedCut** is 213-native signed Cut layer via the pair representation
`SignedCut := Cut × Cut`.  Sign tracking is purely **structural** —
no new substrate primitive.  All operations reduce to `cutSum` +
`cutMul` on the components.

SignedCut is the **first Cayley-Dickson level** on Real213 cuts:
- L0 = Cut (unsigned)
- L1 = SignedCut := Cut × Cut (signed)
- L2 = ComplexCut := SignedCut × SignedCut (complex)
- ...

At each level the CD-doubling is structural; the algebra-tower
chapter (`theory/math/cayley_dickson/algebra_tower.md`) covers the
abstract level-N structure, this chapter covers the concrete
SignedCut level + its CD-doubled descendants.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/SignedCut/` (35 files, 6 sub-clusters)
- **Umbrella**: `SignedCut.lean`
- **∅-axiom status**: PURE

### Sub-cluster organization

| Sub-cluster | Files | Topic |
|---|---|---|
| `Core/` | 9 | Core / Algebra / Inv / UnifiedGenericInv / Equivalence / Capstones |
| `CD/` | 6 | CD-doubling: Conjugation, LevelOps, MulRule, Norm, Tower{Capstone, Level} |
| `Hurwitz/` | 4 | HurwitzCeiling, ExactL1, Failure, NormProduct |
| `Level/` | 5 | Level25Residual, Level25Capstone, Level26Absence, G38FinalCapstone, G39Capstone |
| `Bridge/` | 5 | Bridge/Capstone + FanoK32Bridge + FanoPlane + GenericGeomBridge |
| `Octonion/` | 6 | Octonion + Quaternion mul rules + tables + NonAssociativity |

## The narrative

### Sign as a pair

Classical signed integers `ℤ` are constructed as `ℕ × ℕ / ~`
(equivalence: `(a, b) ~ (c, d) ↔ a + d = b + c`).  213 keeps the
pair representation **without quotienting**:

```
SignedCut := Cut × Cut    -- (positive part, negative part)
```

Operations:
- `(a, b) + (c, d) := (a + c, b + d)`
- `(a, b) · (c, d) := (a·c + b·d, a·d + b·c)`
- `(a, b) ~ (c, d) ↔ a + d = b + c` (equivalence, not quotient)

Equality on SignedCut is `signedEq`, not propositional equality.
This **avoids the propext load** that ℤ-as-quotient would
require.

### Level 25 closure (G37/G38)

The CD tower on SignedCut closes at level 25:
- L25: full CD-doubled signed structure
- L26: **absent** — beyond the resolution limit `N_U = 5²⁵`

`Level/Level25Residual.lean` and `Level26Absence.lean` prove the
absence directly: any putative L26 element reduces to a smaller
level under the resolution-limit reading.

`G38FinalCapstone.lean` bundles the unified 25-level algebra —
all CD-derived structures up to L25 exist within SignedCut's
machinery without external import.

### Octonion non-associativity (G39)

At L3 (octonion level), associativity drops.  `Octonion/NonAssociativity.lean`
provides the **explicit witness**:

```
(u · v) · w ≠ u · (v · w)   for specific octonion triples
```

decided by computing both sides on representative SignedCut^8
elements.  This is the **first concrete non-associativity witness**
in DRLT's 213-native algebra.

### Hurwitz layer

`Hurwitz/` proves the Hurwitz norm-multiplicativity `|uv|² =
|u|² · |v|²` for SignedCut and its CD-doubled descendants.
`HurwitzCeiling` gives the L1 exact identity; `NormProduct`
extends to higher levels; `Failure` documents where the identity
**fails** (beyond Hurwitz's theorem-determined levels).

### Bridge layer

`Bridge/` provides bridges from SignedCut to other geometric
structures: Fano plane (7-point projective geometry of octonions),
FanoK32 (Fano ↔ K_{3,2}^{(c=2)} structural bridge),
GenericGeomBridge (abstract geometric bridge interface).

## Research-note provenance

Three notes (`G37`, `G38`, `G39`) — archived to
`research-notes/archive/discrete_geometry/` (previous batch).

## Open frontier

- **CD level beyond L25**: per the resolution limit, none — but
  reformulating "beyond" structurally requires the next-resolution
  layer (currently outside DRLT scope)
- **Hurwitz failure characterization**: `Failure.lean` documents
  specific failures; a parametric "when does Hurwitz fail at level
  N" theorem is open
- **Non-associativity quantification**: G39 gives one witness; a
  characterization of the obstruction at each L ≥ 3 is open

## How to verify

```bash
cd lean
lake build E213.Lib.Math.SignedCut
python3 tools/scan_axioms.py Lib/Math/SignedCut
```
