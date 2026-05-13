# `Lib/Math/ModArith/` — modular arithmetic + CRT

213-native modular arithmetic: Bézout, GCD, Euclidean algorithm,
join-coprime, CRT (via Lens), per-modulus pure-Nat instances.

## Files (9)

### Bézout / GCD / Euclidean (5)
  - `JoinBezout.lean`     — Bézout's identity as join
  - `JoinCoprime.lean`    — coprime characterisation
  - `JoinEquivGCD.lean`   — equivalence ↔ GCD
  - `JoinEuclidean.lean`  — Euclidean algorithm
  - `JoinGCD.lean`        — GCD via join
  - `JoinExample.lean`    — concrete worked example

### CRT
  - `LensCRT.lean`        — Chinese Remainder Theorem via Lens

### Per-mod Nat instances
  - `PureNatMod3.lean`    — mod-3 PureNat instance
  - `PureNatMod5.lean`    — mod-5 PureNat instance

## Where to add new files

  - New algorithmic GCD / Bézout result   → `Join<algorithm>.lean`
  - New per-modulus Nat instance          → consider consolidating
                                             into `PureNatMod<N>.lean`
                                             (or fold into a single
                                             `PureNatMod.lean` per
                                             CLAUDE.md rule 7)
  - CRT / Lens variant                     → `LensCRT`

## Companion clusters

  - `Meta/Nat/`            — ring-independent Nat helpers
  - `Lens/Instances/Leaves/Mod3`,
    `Lens/Instances/Leaves/ModNat` — Lens-side mod constructions
