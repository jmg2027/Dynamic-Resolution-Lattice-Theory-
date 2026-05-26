# G147 — Promotion: G140 PGeneratesNat + G138 Pattern B/D

**Date**: 2026-05-26
**Status**: PROMOTED (essay + chapters confirmed)

## What was promoted

Three independent results formally linked through a single
higher-insight essay:

### 1. G140 — P generates all of ℕ

- **Lean**: `E213.Lib.Math.Mobius213.Px.PGeneratesNat`
- **Capstone**: `pgen_iff_pos : ∀ n, PGen n ↔ n ≥ 1`
- **Method**: Chicken McNugget (Frobenius) for gcd(NT, NS) = gcd(2, 3) = 1
- **Depth theory**: `minDepth` gives optimal decomposition depth for any n
- **Structural necessity**: Q² = P, gcd(Fₙ, Fₙ₊₁) = 1 → coprimality forced
- **Research note**: `research-notes/G140_P_generates_all_nat.md`

### 2. G138 Pattern B — Sym(3) spine

- **Theory chapter**: `theory/math/sym3_spine.md`
- **Capstone**: `X1_sym3_cross_frame_capstone` (PURE)
- **Content**: 4-way reading of `8 = 2·trivial ⊕ 3·standard`:
  1. K₃,₂² cohomology H¹ rank = 8
  2. 8 Thurston geometries (3 iso + 5 aniso)
  3. Gluon octet dim adj SU(3) = 8
  4. Akbulut cork signed orbits on 8-dim H¹
- **Structural origin**: Sym(3) = Aut({3 forced S-vertices})

### 3. G138 Pattern D — Nodup as recursive Clause-4

- **Lean**: `E213.Lib.Math.Cohomology.NodupAsClause4`
- **Capstone**: `nodup_iff_clause4Nodup : l.Nodup ↔ IsClause4Nodup l`
- **Method**: Induction on list; forward (Nodup → ∀-form) + backward
  (∀-form → Nodup) via PURE Lean without propext
- **Pattern #9 upgrade**: from one instance (`AliveDerivation`) to two;
  promotes the recursive-Clause-4-application from example to methodology
- **Sanity checks**: empty list, 3-element duplicate witness

## Higher-insight connection

The three results converge at K₃,₂²:

- **PGeneratesNat** shows P's additive closure covers ℕ — the
  algebraic axis is universal.
- **Sym(3) spine** shows the same P (via trace = NS = 3) generates
  the symmetry group whose representation decomposes H¹ — the
  cohomology axis structure is P-derived.
- **NodupAsClause4** shows that the face-level no-duplicate condition
  (essential for well-defined cochains on K₃,₂²) is not an imported
  predicate but Clause-4 read at list granularity — the axiom itself
  generates the predicate structure.

Together: P generates the numbers (G140), the symmetry (Pattern B),
and the predicate logic (Pattern D) of K₃,₂² cohomology.  The
framework is self-generating at three independent levels.

## Promotion essay

`theory/essays/k32_cohomology_simplex_higher_insight.md` — the
canonical essay tying G140 + G138 B + G138 D with cross-frame
convergence table (5 surfaces) and constructive-accessibility
landing (7 PURE theorems).

## Promotion status of G138 patterns

| Pattern | Status | Artifact |
|---------|--------|----------|
| A — Modulus-functor 4-way | Open (frontier) | — |
| **B — Sym(3) spine** | **CLOSED + PROMOTED** | `theory/math/sym3_spine.md` |
| C — Cut-off meta-methodology | Open (frontier) | — |
| **D — Nodup as Clause-4** | **CLOSED + PROMOTED** | `NodupAsClause4.lean` |
| E — Int.NonNeg refactoring | Open (Tier 5.1) | — |
| F — Multiplicity doctrine | Open (frontier) | — |

## Cross-references

- `research-notes/G138_post_merge_corpus_synthesis.md` — parent note
- `research-notes/G140_P_generates_all_nat.md` — P-generation detail
- `theory/essays/k32_cohomology_simplex_higher_insight.md` — promotion essay
- `theory/math/sym3_spine.md` — Pattern B chapter
- `lean/E213/Lib/Math/Cohomology/NodupAsClause4.lean` — Pattern D
- `lean/E213/Lib/Math/Mobius213/Px/PGeneratesNat.lean` — G140
- `lean/E213/Lib/Math/Mobius213/Mobius213K32Bridge.lean` — P ↔ K₃,₂²
