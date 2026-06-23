# `Lib/Math/NumberTheory/ModArith/` — modular arithmetic + CRT

213-native modular arithmetic: Bézout, GCD, Euclidean algorithm,
join-coprime, CRT (via Lens), per-modulus pure-Nat instances,
multiplicative order / primitive roots, quadratic reciprocity
(Euler / Gauss / Zolotarev), Wilson, character orthogonality, the
quadratic extension `F_{p²} = F_p[√5]`, and Eisenstein cubic structure.

## Files (62)

### Bézout / GCD / Euclidean (6)
  - `JoinBezout.lean`     — Bézout's identity as join
  - `JoinCoprime.lean`    — coprime characterisation
  - `JoinEquivGCD.lean`   — equivalence ↔ GCD
  - `JoinEuclidean.lean`  — Euclidean algorithm
  - `JoinGCD.lean`        — GCD via join
  - `JoinExample.lean`    — concrete worked example

### Explicit-Nat Bézout / FLT (3)
  - `ModBezout.lean`           — explicit-Nat xgcd + Bezout coefficients
  - `ModBezoutInvariant.lean`  — universal modular inverse via Bezout
  - `UniversalFLT.lean`        — Fermat's Little Theorem (universal in p)

### CRT + Lens meet (4)
  - `LensCRT.lean`         — Chinese Remainder Theorem via Lens
  - `LensCRTGeneral.lean`  — general CRT via Lens
  - `CRTReconstruction.lean` — CRT reconstruction map
  - `LensLcmMeet.lean`     — lcm as Lens meet

### Per-mod Nat instances + division (3)
  - `PureNatMod3.lean`     — mod-3 PureNat instance
  - `PureNatMod5.lean`     — mod-5 PureNat instance
  - `CenteredDivision.lean` — centered (balanced) division

### Multiplicative order / primitive root (9)
  - `MulOrder.lean`        — multiplicative order
  - `MaxOrder.lean`        — maximal order
  - `OrderPow.lean`        — order under powers
  - `CoprimeOrder.lean`    — order of coprime residues
  - `EveryOrdDvdMax.lean`  — every order divides the maximal
  - `PrimitiveRoot.lean`   — primitive-root existence
  - `NonFixedExists.lean`  — non-fixed element existence
  - `FermatFixedPoint.lean` — Fermat fixed-point structure
  - `DiscreteLogParity.lean` — discrete-log parity

### Euler criterion / quadratic reciprocity (10)
  - `EulerCriterion.lean`      — Euler's criterion
  - `EulerConverse.lean`       — converse direction
  - `EulerFirstSupplement.lean` — first supplement (−1)
  - `SecondSupplement.lean`    — second supplement (2)
  - `GaussLemma.lean`          — Gauss's lemma
  - `LegendreMultiplicative.lean` — Legendre symbol multiplicativity
  - `QuadraticReciprocity.lean` — quadratic reciprocity law
  - `QRDescentFrame.lean`      — QR descent frame
  - `QRNegOne.lean`            — QR for −1
  - `QPart.lean`               — quadratic-part extraction

### Zolotarev (6)
  - `Zolotarev.lean`           — Zolotarev's lemma (Legendre = perm sign)
  - `ZolotarevConverse.lean`   — converse
  - `ZolotarevCycle.lean`      — cycle structure
  - `ZolotarevMuBridge.lean`   — μ bridge
  - `ZolotarevReduction.lean`  — reduction
  - `ZolotarevSign.lean`       — sign computation

### Wilson (3)
  - `WilsonTheorem.lean`   — Wilson's theorem
  - `WilsonConverse.lean`  — converse (primality)
  - `WilsonInverse.lean`   — self-inverse pairing

### Character orthogonality (2)
  - `CharacterOrthogonality.lean`       — character orthogonality
  - `CyclicCharacterOrthogonality.lean` — cyclic-group case

### Field / Frobenius / F_{p^k} (7)
  - `FieldIffPrime.lean`         — ℤ/n is a field ⟺ n prime
  - `Frobenius.lean`             — Frobenius endomorphism
  - `FrobeniusNonRepresentable.lean` — non-representable witness
  - `FP2Sqrt5.lean`              — F_{p²} = F_p[√5]; reused by the
                                    Pell-Fibonacci closures in DyadicFSM/UniversalPhase33
  - `FP2SqrtD.lean`              — F_{p²} = F_p[√d] (general d)
  - `ValuationAlg.lean`          — algebraic valuation lemmas
  - `CoprimeMultiplicative.lean` — coprime-multiplicative structure

### Eisenstein / cubic (3)
  - `EisensteinCubeRoot.lean`     — Eisenstein cube root of unity
  - `EisensteinFormCharacter.lean` — Eisenstein form character
  - `CubeFromFLT.lean`            — cubic structure from FLT

### Quadratic forms / sums of squares (6)
  - `SqPlusOneFrame.lean`         — x²+1 frame
  - `SqMinusTwoFrame.lean`        — x²−2 frame
  - `SumOfSquaresObstruction.lean` — sum-of-squares obstruction
  - `PrimeSquareFactor.lean`      — prime square factor
  - `MarkovPrimeFactor.lean`      — Markov prime factor
  - `LucasTheorem.lean`           — Lucas' theorem (binomial mod p)

## Where to add new files

  - New algorithmic GCD / Bézout result   → `Join<algorithm>.lean`
  - New per-modulus Nat instance          → consolidate into
                                             `PureNatMod<N>.lean` (CLAUDE.md rule 7)
  - CRT / Lens variant                     → `LensCRT*`
  - QR / Zolotarev / Wilson / order        → next to the matching cluster above
  - FLT / Frobenius / F_{p^k} extensions   → next to `FP2Sqrt5.lean`

## Companion clusters

  - `Meta/Nat/`            — ring-independent Nat helpers
  - `Lens/Instances/Leaves/Mod3`,
    `Lens/Instances/Leaves/ModNat` — Lens-side mod constructions
