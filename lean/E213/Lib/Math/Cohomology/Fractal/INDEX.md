# `Cohomology/Fractal/` — parametric configuration count + cut-offs

The parametric bare-combinatorics configuration count
`configCountD d n = d^(d^n)` (no level privileged), its modular
fingerprints, the Aurifeuillean correspondence, and the
sequence-family cardinality cut-offs.

## configCount core

  - `ConfigCount.lean` — `configCountD d n = d^(d^n)` parametric
    count; `configCount 2 = 5²⁵` as arithmetic theorem
  - `ConfigCountModular.lean` — modular reductions
  - `EventualPeriodicity.lean` — eventual periodicity at coprime
    (d, p)

## Aurifeuillean correspondence

  - `ConfigCountAurifeuillean.lean` — Aurifeuillean handle on
    `configCount 2 + 1`
  - `ConfigCountAurifeuilleanParam.lean` — parametric:
    `∀ n ≥ 1, 521 ∣ 5^(5^n) + 1`
  - `AurifeuilleanCutoff.lean` / `AurifeuilleanFullCutoff.lean` —
    Hunter ⇔ Aurifeuillean cut-off (m = 1; refined)
  - `AurifeuilleanDepth2Cutoff.lean` /
    `AurifeuilleanDepth2PowCutoff.lean` — depth-2 cut-offs
    (restricted; outer-pow for catalogue prime 521)
  - `AurifeuilleanLUnbounded.lean` — L unboundedness (bounded chain)

## Sequence-family cut-offs (cardinality + modular fingerprint pairs)

  - `FibonacciCutoff.lean` / `FibonacciModular.lean`
  - `LucasCutoff.lean` / `LucasModular.lean`
  - `PellCutoff.lean`
  - `TribonacciCutoff.lean` / `TribonacciModular.lean`
  - `JacobsthalCutoff.lean` / `JacobsthalModular.lean`
  - `PadovanCutoff.lean` / `PadovanModular.lean`
  - `NarayanaCutoff.lean` / `NarayanaModular.lean`

## Hunter catalogue + capstones

  - `HunterComplexity.lean` — Hunter complexity measure
  - `HunterAtomicClosure.lean` — atomic prime catalogue, mod-p
    closure analysis
  - `PisanoGridCapstone.lean` — Pisano-analogue grid master capstone
  - `AltPrimitiveSet.lean` — cut-off principle parametric in the
    primitive set

## Fractal-simplex levels

  - `Level.lean` — K_{5^L} cohomology at L levels
  - `V25.lean` — level 2, K_{25}

## Physics-facing

  - `AlphaGUT.lean` — fractal-cohomology reformulation of α_GUT

## Top-level

  - `Fractal.lean` umbrella aggregator (one level up)
