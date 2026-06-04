# `Lens/Number/` — Raw-derived number systems

Each module is a `Raw.fold` catamorphism output reified as a
number system.  Per ARCHITECTURE.md: catamorphism + data choice =
Lens-layer artifact.

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
                   `Lens.Number.Nat213.Tower.NatPairToInt`;
                   promote to a sibling `Int213/` sub-cluster
                   once mature).
  - `Rat213/`    — ℚ via multiplicative quotient (currently in
                   `Nat213/Tower/NatPairToQPos`).
  - `Real213/`   — ℝ via cuts / Cauchy seqs over Nat213
                   (currently in `Lib/Math/NumberSystems/Real213`; candidate for
                   migration once mature).

## Where to add new files

  - New Raw-derived number system  → `Number/<Type>/`
  - Bridge between representations → `<Type>/Bridge.lean`
  - Lenses witness                 → `<Type>/Lenses.lean`

## Discipline

`Lens` ring imports only `Theory` + `Term` + `Meta` (per
ARCHITECTURE).  Number modules can use `Theory.Raw.API` (incl.
`Theory.Raw.Endomorphic` for closed-Raw catamorphism) freely; the
former `Theory.Closed.Bool213` is now `Lens.Bool213` (sibling
sub-cluster).
