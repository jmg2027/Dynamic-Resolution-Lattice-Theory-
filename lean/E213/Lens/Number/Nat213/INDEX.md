# `Lens/Number/Nat213/` — 213-native positive naturals

Five representations of ℕ₊ + bridges + chart generalisation + lens
characterisations + numbering / cut / tower outgrowth.

## Files (12)

### Representations

  - `Raw.lean`             — Method A Raw chart (canonical).
                             `one := Raw.a`, `succ n := slashOrSelf n
                             Raw.b`, `numeral : Nat → Raw`,
                             `value : Raw → Nat`.  **Chart structure
                             only — no Raw-side arithmetic** (per
                             Option C of the lens-emergence
                             roadmap).  Arithmetic lives on `Nat`.
  - `Peano.lean`           — Inductive `Nat213 | one | succ` with its
                             own arithmetic.  Ergonomic parallel
                             representation; not lens-derived.
  - `Core.lean`            — Lens-derived `{ n : Nat // 1 ≤ n }`
                             Nat-subtype carrier.
  - `Chain.lean`           — Raw-subtype `{ r : Raw // IsMethodAChain r }`
                             carrier.  Operations route through `Nat`
                             (Option C realisation); `toNat` is a
                             `+` / `*` homomorphism.
  - `ChartGeneral.lean`    — Parameterised chart `chartChain (r₀ r' :
                             Raw) (h : r₀ ≠ r') : Nat → Raw`.
                             Default `(Raw.a, Raw.b)` chart recovers
                             `Raw.numeral` (Option D).

### Bridges

  - `Bridge.lean`            — `toRaw : Peano.Nat213 → Raw` chart
                               embedding; `value_toRaw` projection
                               bijection; value-level additive /
                               multiplicative homomorphism
                               (`value_toRaw_add`, `value_toRaw_mul`).
  - `ChainCoreBridge.lean`   — `Chain ↔ Core` isomorphism: `Chain.toCore`
                               (Raw-subtype → Nat-subtype) +
                               `Nat213.toChain` (inverse, via
                               `Chain.numeral`).  Both round-trips
                               proved.

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
                             `Raw → Raw → Raw`; vertical projection.

### Tower (ℕ-pair / ℕ-triple → other number systems via quotient)

  - `Tower/NatPairToInt.lean`
                           — ℤ via additive diagonal quotient.
  - `Tower/NatPairToQPos.lean`
                           — ℚ₊ via multiplicative quotient on
                             `(Peano.Nat213 × Peano.Nat213)`.
  - `Tower/NatTripleToZ2.lean`
                           — ℤ² via 3-axis projection.

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

**Option C refactor (2026-05-18)**: Raw-side arithmetic (`add, mul,
addAux, mulAux, one_add, one_mul, add_succ_left, mul_succ_left,
leavesCountRaw, ...`) deleted from `Raw.lean`.  Arithmetic now lives
on `Nat` and routes through the chart via `Raw.numeral` /
`Raw.value`.  `Chain.lean` rewritten to use Nat-routed operations.
`Bridge.lean` slimmed to chart bijection + value-level homomorphism.
`Lib/Math/NumberSystems/Real213/Cauchy/ChainToCut.lean` migrated to use Peano
arithmetic via the new `value_toRaw_{add,mul}` (the lens-emergence
roadmap, Option C).
