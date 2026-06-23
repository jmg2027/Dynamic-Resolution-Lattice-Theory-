# `Lib/Math/NumberTheory/ModArith/` — modular arithmetic + CRT

213-native modular arithmetic: Bézout, GCD, Euclidean algorithm,
join-coprime, CRT (via Lens), per-modulus pure-Nat instances.
G119 marathon (merged 2026-05-22) extends with explicit-Nat
Bezout, universal FLT, and the quadratic extension F_{p²} = F_p[√5].

## Files (13)

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

### G119 marathon — Bezout / FLT / F_{p²} (4)
  - `ModBezout.lean`           — explicit-Nat xgcd + Bezout coefficients
  - `ModBezoutInvariant.lean`  — universal modular inverse via Bezout
  - `UniversalFLT.lean`        — Fermat's Little Theorem (universal in p):
                                  freshman's dream → binomial theorem →
                                  FLT primary → FLT main
  - `FP2Sqrt5.lean`            — F_{p²} = F_p[√5]: quadratic field
                                  extension of F_p adjoining √5, with
                                  Frobenius `x ↦ x^p` as a ring
                                  endomorphism; reused by the
                                  Pell-Fibonacci universal closures in
                                  DyadicFSM/UniversalPhase33

## Where to add new files

  - New algorithmic GCD / Bézout result   → `Join<algorithm>.lean`
  - New per-modulus Nat instance          → consider consolidating
                                             into `PureNatMod<N>.lean`
                                             (or fold into a single
                                             `PureNatMod.lean` per
                                             CLAUDE.md rule 7)
  - CRT / Lens variant                     → `LensCRT`
  - FLT / Frobenius / F_{p^k} extensions  → next to `FP2Sqrt5.lean`

## Companion clusters

  - `Meta/Nat/`            — ring-independent Nat helpers
  - `Lens/Instances/Leaves/Mod3`,
    `Lens/Instances/Leaves/ModNat` — Lens-side mod constructions
