# CayleyDickson — Module Index (sub-organized 2026-05-13)

213-native Cayley–Dickson algebra tower.  57 files in 5 sub-clusters.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `Tower/` | 12 | CD-doubling iteration (CDDouble, CDTower, F2CDTower, AlgebraTowerCapstone/Asymptote, TowerFixedPoint, UniversalOrderGrowth{,C}, Order4Monopoly_L{4,5,6}T, UniversalInduction) |
| `Integer/` | 27 | ℤ-quad / ℤ-quartic integer rings (ZI*, ZOmega*, ZSqrt*, Z2Instance, Hurwitz213, ShiftRule_ZI_L3) |
| `Levels/` | 10 | CD levels 3+ (Cayley/Sedenion/Pathion/Trigintaduonion {,Heavy,Order4Monopoly}) |
| `Lipschitz/` | 4 | Lipschitz quaternion order family |
| `Misc/` | 4 | helpers (QuadIdentities, R5Vacuity, TypeAResidualClosedForm, TypeE_Rejection) |

## Top-level

`CayleyDickson.lean` — umbrella aggregator.

## Architecture notes

- All Heavy files use generic `Algebra213.IntegerNormed213.normSq_mul`
  (Meta/Algebra213) — replaces brute-force `hurwitz_ring` polynomial
  expansion.
- ZI / Lipschitz / Cayley / Sedenion chain progressively drops
  commutativity / associativity per CD-doubling step (CDTower
  documents).

PURE 진행: see STRICT_ZERO_AXIOM.md.
