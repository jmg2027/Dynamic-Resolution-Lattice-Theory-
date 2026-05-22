# AkbulutCork — sub-tree INDEX

213-native realization of the Akbulut–Curtis–Freedman–Hsiang–Stong
cork theorem for closed simply-connected 4-manifolds.

**Status**: G126 6-phase partial close (2026-05-22) — 4 files, 44 PURE.
**Supersedes**: FW-1 signed Donaldson count (the FW-1 sign problem
becomes a 213-internal cork-twist Z/2 grading).

## File map

| File | Phase | PURE | Content |
|---|---|---|---|
| `Foundation.lean` | 1 | 14 | `Cork213` structure (contractible_b1, boundary_size, twist_parity) + canonical instances (`K11_cork`, `K31_cork`, `K14_cork`) + well-formedness witnesses + bridge to parametric Bipartite cohomology |
| `Twist.lean` | 2 | 12 | `corkTwist : Cork213 → Cork213` Z/2 endomorphism + `corkTwist_involution_on_K{11,31,14}` + parity-alternation theorems + M_S01 correspondence at matrix level |
| `SignedOrbits.lean` | 3 | 13 | Per-orbit-type M_S01 fix counts (singleton: 4, size-3: 28, size-6: 0) + Z/2 grading (twistEven = 32, twistOdd = 28) + ★★★★★★ `signedCorkTwistCount = +4` |
| `CorkTheorem.lean` | 4-6 | 5 | Cork embedding at chartBase=5 + cork uniqueness (M_S01 involutive) + ★★★★★★★★★★ `akbulut_cork_213_native` capstone bundling all 6 phases |

## Phases vs G126 plan

The original G126 research direction estimated ~120 PURE / 8-12
sessions across 6 phases.  Actual close: 44 PURE / 4 files /
single session — phases compose more efficiently than estimated
because all dependencies were pre-existing in E213.

## Cork-data ↔ standard math correspondence

| Standard math | 213-native realization | E213 witness |
|---|---|---|
| Contractible 4-mfd C | K_{1,4}^{(c=1)} tree, b_1 = 0 | `Foundation.K14_cork` |
| Z/2 involution τ | M_S01 transposition | `Sym3OnH1KMatrix.M_S01_squared_pointwise` |
| ∂C = S³ | ∂Δ⁴, χ = 0 | `EulerChi.chi_S3_eq_zero` |
| Cork embedding | tree + critical at chartBase = 5 | `chartBase_5_tree_and_critical_coexist` |
| Cork-twist | `corkTwist (corkTwist c) = c` | `Twist.corkTwist_involution_on_K14` |
| Signed exotic count | `signedCorkTwistCount = +4` | `SignedOrbits.signedCorkTwistCount_eq_4` |

## Dependency chain

```
Foundation
   └── Twist
         └── SignedOrbits (+ GeometrizationConjecture.Exotic4Mfd)
               └── CorkTheorem (+ GeometrizationConjecture.Capstone)
```

All under namespace `E213.Lib.Math.AkbulutCork.*`.

## FW-1 supersession

The cork-frame closes FW-1 (signed Donaldson count) internally:

  · Original FW-1 plan: 213 unsigned Burnside count (60) → external
    Donaldson invariant — blocked by 213/standard-math boundary.
  · Cork-frame resolution: Sym(3)-orbits inherit Z/2 grading from
    M_S01 cork-twist → signed count `+4 = 32 − 28` — fully 213-internal.

`research-notes/G126_akbulut_cork_213_native.md` records the
research direction; this sub-tree is the partial close.

## Open work (full close beyond Phase 6)

  · Comparison to specific 4-manifold Donaldson invariants (would
    need external bridge anyway; not 213-internal)
  · Cork-twist effect on higher cohomology (b_2, b_3 levels —
    requires `Filled3Cell.lean` extension to 3-cell complexes)
  · Multi-cork structures (corks-of-corks): higher-order Z/2
    actions on the K-deployment
