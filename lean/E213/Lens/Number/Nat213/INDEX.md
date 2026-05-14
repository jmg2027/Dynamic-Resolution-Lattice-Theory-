# `Lens/Number/Nat213/` — 213-native positive naturals

Two equivalent representations of ℕ₊ + their bridge + lens
characterisations + numbering / cut / tower outgrowth.

## Files (8)

### Representations

  - `Raw.lean`             — Method A Raw chain (canonical).
                             `one := Raw.a`, `succ n := slashOrSelf n
                             Raw.b`.  No new type — just operations on
                             `Raw`.  Closed-codomain `Raw.fold` arity
                             output.
  - `Peano.lean`           — Inductive `Nat213 | one | succ`.
                             Ergonomic Peano representation.

### Bridge

  - `Bridge.lean`          — `toRaw : Peano.Nat213 → Raw` isomorphism;
                             add/mul homomorphism; `value` /
                             `leavesCountRaw` commute with `toNat`;
                             fixed-point characterisation of
                             `leavesCountRaw`.

### Lens-theoretic

  - `Lenses.lean`          — characterisation of `Raw → Peano.Nat213`
                             lenses (G66 — multiplicity, swap-invariance,
                             infinite family).
  - `AtomicityCorrespondence.lean`
                           — `NS + NT = 3 + 2 = 5` realised at
                             type-signature level (Raw constructors +
                             Peano constructors).

### Numbering / cut

  - `NumberingSystem.lean` — meta pattern `(Z, C)`; Method A as
                             canonical numbering; iso via foldRaw.
  - `RawCut.lean`          — Lean-free cut prototype
                             `Raw → Raw → Raw`; vertical projection
                             parallel to `leavesCountRaw` /
                             `booleanProj`.

### Tower (ℕ-pair / ℕ-triple → 다른 number system via quotient)

  - `Tower/NatPairToInt.lean`
                           — ℤ via additive diagonal quotient
                             (Lean `Nat` 위; G62).  `a + d = b + c`.
  - `Tower/NatPairToQPos.lean`
                           — ℚ₊ via multiplicative quotient on
                             `(Peano.Nat213 × Peano.Nat213)` — G73
                             additive↔multiplicative quotient parallel.
  - `Tower/NatTripleToZ2.lean`
                           — ℤ² via 3-axis projection (Lean Nat 위;
                             Eisenstein basis).  `(a, b, c) ↦ (a - c,
                             b - c)`.  Exploratory.

세 Tower 모두 동일 syntactic container (Nat-pair 또는 Nat-triple)
에서 출발해 다른 quotient relation 으로 분기.  NatPairToQPos 는
Peano Nat213 사용; NatPairToInt / NatTripleToZ2 는 Lean Nat 사용
(추후 Peano-rebase 후보).

## Top-level

  - `Lens/Number/Nat213.lean` aggregator.

## Where to add new files

  - New representation             → `Nat213/<Name>.lean`
  - Bridge between representations → extend `Bridge.lean`
  - Tower construction (Int/Rat/…) → `Tower/<Type>.lean`

## Discipline

All theorems ∅-axiom (verified via `tools/scan_axioms.py`).
Migrated 2026-05-14 from `Theory.{Closed.Nat213, Nat213,
Tower.NatPairToQPos, Closed.{Nat213Bridge, NumberingSystem, RawCut}}`
under the principle "Raw + catamorphism choice = Lens-layer
artifact".
