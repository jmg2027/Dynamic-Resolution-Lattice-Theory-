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

### Tower

  - `Tower/NatPairToQPos.lean`
                           — ℚ₊ via multiplicative quotient on
                             `(Peano.Nat213 × Peano.Nat213)` — G73
                             additive↔multiplicative quotient parallel.

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
