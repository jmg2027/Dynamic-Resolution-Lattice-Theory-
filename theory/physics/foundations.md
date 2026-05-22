# Physics Foundations

**Status**: Closed (22 files).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.  Complements `theory/physics/foundations/atomic_constants.md`
(C2 uniqueness) — this chapter covers the rest of `Foundations/`.

## Overview

Physics scaffolding primitives: **N_resolution cardinality**
(`d^(d²) = 5²⁵` derived from fractal lens), atomic constants
(referenced; closed in atomic_constants chapter), finiteness
witnesses, resonance structure, number-theoretic atomic-integer
patterns (Fibonacci, golden ratio, Koide).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Foundations/` (22 files)
- **Umbrella**: `Foundations.lean`
- **∅-axiom status**: PURE

| Group | Files | Topic |
|---|---|---|
| N_resolution scaffold | 7 | `NResolutionFromFractal` + `NResolutionFractalDepth` + helpers |
| AtomicConstants | 5 | (already chaptered: `atomic_constants.md`) |
| Finiteness | ~3 | finite-witness layer |
| Resonance | ~3 | resonance structure |
| Integer patterns | ~4 | Fibonacci, golden ratio, Koide |

## Narrative

`N_resolution = d^(d²) = 5²⁵` is the **fractal-lens output** at
fractal level 2: take d = 5 (atomic dim), iterate d² = 25 times,
get d^25 = 5²⁵ distinguishable points.  This is the **count-Lens
readout** of the universe-chain's terminal cardinality (per
`seed/RESOLUTION_LIMIT_SPEC.md`).

Other foundational primitives:
- **Finiteness witnesses**: any DRLT observable's value bracket
  has explicit finite-precision representation at the chosen
  `configCount` family-evaluation level (`configCount 2 = 5²⁵`
  for canonical physics-side work)
- **Resonance structure**: which integer ratios admit resonant
  interpretations (matches CKM, mass ratios, ...)
- **Koide formula**: lepton mass relation `(m_e + m_μ + m_τ)² /
  (√m_e + √m_μ + √m_τ)² = 2/3`; DRLT-derivable from atomic
  primitives

## Connection

- `theory/physics/foundations/atomic_constants.md` — C2 sub-chapter
- `seed/RESOLUTION_LIMIT_SPEC.md` — `N_U = 5²⁵` canonical
- `theory/physics/atomic_base.md` — atomic primitive layer
