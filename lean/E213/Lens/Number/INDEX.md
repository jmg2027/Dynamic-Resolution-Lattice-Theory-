# `Lens/Number/` — Raw-derived number systems

Each module is a `Raw.fold` catamorphism output reified as a
number system.  Per ARCHITECTURE.md (2026-05-13): catamorphism +
data choice = Lens-layer artifact.  Migrated from
`Theory.Closed.{Nat213, Nat213Bridge, RawCut, NumberingSystem}` +
`Theory.Nat213.*` + `Theory.Tower.NatPairToQPos` on 2026-05-14.

## Sub-clusters

  - `Nat213/`    — 213-native positive naturals
                   (Method A Raw chain — canonical;
                    inductive Peano — ergonomic;
                    Bridge — isomorphism;
                    Lenses / AtomicityCorrespondence;
                    NumberingSystem — meta `(Z, C)` pattern;
                    RawCut — Lean-free cut prototype;
                    Tower/NatPairToQPos — ℚ₊ via mul-quotient).

## Future

  - `Int213/`    — ℤ via additive-axis quotient on `Nat213 × Nat213`
                   (currently prototyped in
                   `Theory.Tower.NatPairToInt`; promote to Lens
                   once Peano-rebased).
  - `Rat213/`    — ℚ via multiplicative quotient (currently in
                   `Nat213/Tower/NatPairToQPos`).
  - `Real213/`   — ℝ via cuts / Cauchy seqs over Nat213
                   (currently in `Lib/Math/Real213`; candidate for
                   migration once mature).

## Where to add new files

  - New Raw-derived number system  → `Number/<Type>/`
  - Bridge between representations → `<Type>/Bridge.lean`
  - Lenses witness                 → `<Type>/Lenses.lean`

## Discipline

`Lens` ring imports only `Theory` + `Term` + `Meta` (per
ARCHITECTURE).  Number modules can use `Theory.Raw` /
`Theory.Closed.{Bool213, FoldRaw}` freely, but must NOT reach into
Theory.Internal.
