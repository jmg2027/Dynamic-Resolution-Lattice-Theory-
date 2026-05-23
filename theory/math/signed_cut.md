# SignedCut — Sign Extension on Real213 Cuts

**Status**: Closed (35 files in 6 sub-clusters).

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

### Level 25 closure

The CD tower on SignedCut closes at level 25 (the family-evaluation
level chosen for physics-side readings, `configCount 2 = 5²⁵`):
- L25: full CD-doubled signed structure
- L26: **absent** — exceeds the level-2 family evaluation
  `configCount 2 = 5²⁵` (per N_U re-derivation Round 3: the boundary is a
  level-choice, not a privileged "resolution limit cap")

`Level/Level25Residual.lean` and `Level26Absence.lean` prove the
absence directly: any putative L26 element reduces to a smaller
level under the resolution-limit reading.

`G38FinalCapstone.lean` bundles the unified 25-level algebra —
all CD-derived structures up to L25 exist within SignedCut's
machinery without external import.

### Octonion non-associativity

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

## Hurwitz dichotomy — closed (HurwitzDichotomy.lean, 26 PURE)

`Lib/Math/SignedCut/Hurwitz/HurwitzDichotomy.lean` quantifies the
classical Hurwitz theorem as a parametric Nat-decidable predicate:

  `hurwitzAdmissible n := decide (n ≤ 3)`

Reading: CD level `n` is Hurwitz-admissible (carries
`‖z·w‖² = ‖z‖² · ‖w‖²`) iff `n ≤ 3`.  The four admissible levels
correspond to ℝ (n=0), ℂ (n=1), ℍ (n=2), 𝕆 (n=3); level 4
(sedenions 𝕊) is the first failure.

  · Decision table: `hurwitz_admissible_{0..3} = true`,
    `hurwitz_fails_{4, 5, 25} = false`.
  · Iff characterisation:
    `hurwitz_admissible_iff : hurwitzAdmissible n = true ↔ n ≤ 3`.
  · Component counts via `levelDim`: `1, 2, 4, 8, 16, ...`
    matching ℝ, ℂ, ℍ, 𝕆, 𝕊.
  · Brahmagupta-Fibonacci magnitude bound at level 1
    (`hurwitz_sample_complex`, `hurwitz_sample_complex_general`).
  · Level 4 non-triviality (`level_4_nontrivial`) from
    `HurwitzFailure.sed_zero_neq_one`.
  · ★★★★ `hurwitz_dichotomy_capstone` — bundles decision table +
    iff + component counts + sample bound + failure witness.

## Non-associativity quantification — closed (NonAssocQuantification.lean, 19 PURE)

`Lib/Math/SignedCut/Octonion/NonAssocQuantification.lean` quantifies
the associativity break as a parametric dichotomy, parallel to
`HurwitzDichotomy`:

  `assocAdmissible n := decide (n ≤ 2)`

CD level `n` is associativity-admissible iff `n ≤ 2`.  The three
admissible levels are ℝ (n=0), ℂ (n=1), ℍ (n=2); level 3
(octonions) is the first break.

  · `assoc_admissible_iff`: `assocAdmissible n = true ↔ n ≤ 2`.
  · Three non-associativity witnesses at L = 3: `(e₁, e₂, e₄)`,
    `(e₂, e₃, e₄)`, `(e₁, e₃, e₄)` — independent basis triples.
  · Three associativity controls at L = 2: `(e₁, e₂, e₃)`,
    `(e₂, e₃, e₁)`, `(e₁, e₂, e₁)` — the (1, 2, 3) Fano sub-line
    closes a quaternion sub-algebra.
  · `isAssocAt a b c` — Bool-valued associator indicator.
  · All six permutations on the (1, 2, 3) line are associative
    (`isAssocAt_quaternion_line`).
  · ★★★★ `non_associativity_quantification_capstone` packages
    decision table + iff + three nonassoc witnesses + three
    assoc controls.

Pairing with `HurwitzDichotomy`: the Cayley-Dickson tower drops
properties in the canonical ladder

  commut (n ≤ 1) → assoc (n ≤ 2) → norm-mult (n ≤ 3)

— three nested Nat-decidable predicates capturing the classical
ZFC characterisation of `ℝ, ℂ, ℍ, 𝕆`.

## Open frontier

- **CD level beyond L25**: not closed at the level-2 `configCount`
  evaluation — but
  reformulating "beyond" structurally requires the next-resolution
  layer (currently outside DRLT scope)
- ~~**Hurwitz failure characterization**~~ — CLOSED via
  `HurwitzDichotomy.lean` (26 PURE) above.
- ~~**Non-associativity quantification**~~ — CLOSED via
  `NonAssocQuantification.lean` (19 PURE) above.

## Rigor — dichotomy ladder strict ordering (14 PURE)

`Lib/Math/SignedCut/DichotomyLadder.lean` consolidates the three
dichotomies into a **strict refinement chain**:

  `commut (n ≤ 1) → assoc (n ≤ 2) → norm-mult (n ≤ 3)`

  · `commutAdmissible n := decide (n ≤ 1)` (new) admits ℝ, ℂ only.
  · `commut_implies_assoc`, `assoc_implies_hurwitz`,
    `commut_implies_hurwitz` — Bool-level implications.
  · `assoc_strictly_extends_commut` — ℍ at n=2 witnesses strict.
  · `hurwitz_strictly_extends_assoc` — 𝕆 at n=3 witnesses strict.
  · `all_fail_at_sedenion` — 𝕊 at n=4 = total collapse.
  · `ladder_population` — exact admitted-set sizes (2, 3, 4).
  · ★★★★★ `dichotomy_ladder_capstone` packages implications +
    strict refinements + sedenion total fail.

Reading: the three CD-loss predicates form a faithful chain — each
strictly stronger than the next; the four normed-division-algebras
(ℝ, ℂ, ℍ, 𝕆) are characterised by exactly where they enter the
ladder.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.SignedCut
python3 tools/scan_axioms.py Lib/Math/SignedCut
```
