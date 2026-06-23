# CayleyDickson — Module Index

213-native Cayley–Dickson algebra tower.  118 files in 5 sub-clusters.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `Tower/` | 42 | CD-doubling iteration (CDDouble, CDTower, F2CDTower, AlgebraTowerCapstone/Asymptote, TowerFixedPoint, UniversalOrderGrowth{,C}, Order4Monopoly_L{4,5,6}T, UniversalInduction, FirstSlashGrounding, …) |
| `Integer/` | 52 | ℤ-quad / ℤ-quartic integer rings (ZI*, ZOmega*, ZSqrt*, Z2Instance, Hurwitz213, HurwitzTower, UnitsToModular, ShiftRule_ZI_L3, …) |
| `Levels/` | 15 | CD levels 3+ (Cayley/Sedenion/Pathion/Trigintaduonion {,Heavy,Order4Monopoly}, SedenionZeroDivisor) |
| `Lipschitz/` | 5 | Lipschitz quaternion order family (incl. LipschitzMoufang) |
| `Misc/` | 4 | helpers (QuadIdentities, R5Vacuity, TypeAResidualClosedForm, TypeE_Rejection) |

## Top-level

`CayleyDickson.lean` — umbrella aggregator.

## Architecture notes

- **Associative layers** (ZI, Lipschitz, ZOmega(Double), ZSqrt/L3T)
  use generic `Algebra213.IntegerNormed213.normSq_mul` (Meta/Algebra213)
  — replaces brute-force `hurwitz_ring` polynomial expansion.
- **Non-associative composition layers** (Cayley = A·L3, ZOmegaQuad =
  C·L4, L4T = B·L4) use `MoufangIntegerNormed213` + the polarization
  framework `Meta/Algebra213/CDDoubleMoufang.lean`: the degree-4
  Hurwitz norm identity is cancelled by the trace condition
  `TraceNormed213` (`a + conj a` central), `cd_normSq_mul` /
  `cd_moufang_norm` bridged per type (`Levels/CayleyMoufang.lean`,
  `Integer/ZOmegaQuadAlgebra213.lean §4`,
  `Integer/ZSqrtMinus2Algebra213.lean §7`).  `CayleyHeavy.normSq_mul`
  now bridges to this (PURE; the `maxHeartbeats 4000000` `hurwitz_ring`
  proof is gone).
- **Octonion alternativity** (`alt_left`/`alt_right`/`flexible`) uses
  the same polarization machinery: `Meta/Algebra213/CDDoubleAlternative.lean`
  proves `cd_alt_left` (hard component identity), `cd_alt_right` (via the
  `conj` anti-automorphism), `cd_flexible` (linearization).
  `CayleyHeavy.{alt_left,alt_right,flexible}` bridge to it — CayleyHeavy
  is now entirely `hurwitz_ring`-free.  (Beyond the octonion layer,
  `Sedenion`/`Trigintaduonion` flexibility still uses `hurwitz_ring`:
  flexibility over a *non-associative* base needs a distinct cubic
  proof, not the associative `cd_flexible`.)
- Beyond the octonion-analog layer (Sedenion, ZOmegaOct, L5T+) norm
  composition genuinely fails (zero divisors): `TraceNormed213` does
  not lift to a non-associative base, so no Moufang norm instance.
- ZI / Lipschitz / Cayley / Sedenion chain progressively drops
  commutativity / associativity per CD-doubling step (CDTower
  documents).

PURE progress: see STRICT_ZERO_AXIOM.md.
