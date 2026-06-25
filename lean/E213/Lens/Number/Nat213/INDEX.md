# `Lens/Number/Nat213/` — 213-native positive naturals + the descent-leg discipline

ℕ₊ as readings of `Raw`'s distinguishing spine, plus an elementary number theory
(divisibility → primes → FTA → infinitude → Chebyshev) computed **entirely over the
Raw-generated `Nat213`** — the **descent leg** made concrete (narrative:
`theory/math/numbersystems/naturals_from_the_spine.md`,
`theory/essays/foundations/raw_and_lens_explained.md`).

## Files (26 + Tower/5)

### Representations

  - `Raw.lean`             — Method A Raw chart (canonical).
                             `one := Raw.a`, `succ n := slashOrSelf n Raw.b`,
                             `numeral : Nat → Raw`, `value : Raw → Nat`.
                             **Chart structure only — no Raw-side arithmetic**
                             (Option C); arithmetic lives on `Nat`/`Peano`.
  - `Peano.lean`           — Inductive `Nat213 | one | succ` with its own
                             arithmetic (`add`/`mul`, no-zero/no-subtraction
                             shape *forced* by the primitive).  The carrier the
                             descent-leg discipline is computed over.
  - `Core.lean`            — Lens-derived `{ n : Nat // 1 ≤ n }` Nat-subtype carrier.
  - `Chain.lean`           — Raw-subtype `{ r : Raw // IsMethodAChain r }` carrier;
                             operations route through `Nat` (Option C); `toNat` is a
                             `+`/`*` homomorphism.
  - `ChartGeneral.lean`    — Parameterised chart `chartChain (r₀ r')`; default
                             `(Raw.a, Raw.b)` recovers `Raw.numeral` (Option D).

### Bridges

  - `Bridge.lean`          — `toRaw : Peano.Nat213 → Raw` chart embedding;
                             `value_toRaw` bijection; value-level `+`/`*` homomorphism.
  - `ChainCoreBridge.lean` — `Chain ↔ Core` isomorphism (both round-trips proved).

### Lens-theoretic

  - `Lenses.lean`          — characterisation of `Raw → Peano.Nat213` lenses
                             (G66 — multiplicity, swap-invariance, infinite family).
  - `AtomicityCorrespondence.lean` — `NS + NT = 3 + 2 = 5` at type-signature level.
  - `SignatureMaps.lean`   — the morphism tower of ℕ⁺'s signature.

### Generation (the descent leg, leg-1)

  - `Generation.lean`      — ℕ₊ is the canonical leaves-Lens reading of iterated
                             distinguishing (`value_eq_leaves`, `succ_is_distinguishing`,
                             `generation_capstone`); the arity-forcing bracket.
  - `Forcing.lean`         — the FTA's carrier is forced by the distinguishing.

### Discipline over `Nat213` (leg-2: number theory generated all the way down)

  - `Order.lean`           — native strict total order `lt` (irrefl, trans, asymm,
                             trichotomy) + non-strict total partial order `le`
                             (refl/trans/antisymm/total), additive + multiplicative
                             monotonicity, native cancellation, square-injectivity
                             (`mul_self_inj`).  No Lean `Nat` order, no `toNat`.
  - `Divisibility.lean`    — `Dvd` over `Nat213`'s own `mul`: a partial order with
                             bottom `one`, no top (`dvd_antisymm`, `dvd_no_top`);
                             refines `le` (`dvd_imp_le`).
  - `Irreducible.lean`     — irreducibility over the Raw-generated ℕ₊.
  - `EuclidUnique.lean`    — Euclid's lemma (`euclid`) over `Nat213`; subtractive
                             gcd existence + multiplicative spec (`gcd_exists_mul`).
  - `Gcd.lean`             — the gcd discipline (`IsGcd`): divisibility is a
                             meet-semilattice — gcd exists + unique + multiplicative
                             law `gcd(c·a,c·b)=c·gcd(a,b)`. Extracted from
                             `gcd_exists_mul`.
  - `Prime.lean`           — irreducible ⟺ prime (`irreducible_iff_prime`), the
                             UFD-defining coincidence.
  - `Factorization.lean`   — every `Nat213` is a product of irreducibles.
  - `FTA.lean`             — the Fundamental Theorem of Arithmetic over `Nat213`.
  - `Infinitude.lean`      — Euclid's theorem (infinitude of primes) over `Nat213`.
  - `ChebyshevLower.lean`  — the Chebyshev lower bound `π(N) ≥ c·N/ln N`.

### Multiplicative system

  - `MultSystem.lean`      — the system multiplication (Pascal/`binom`, window
                             products, the multiplicative-counting layer).
  - `MultSystemValue.lean` — the prime-valued instance (case A): `primesIn`,
                             `listProd`, the window-split toolbox.

### Numbering / cut

  - `NumberingSystem.lean` — meta pattern `(Z, C)`; Method A as canonical numbering.
  - `RawCut.lean`          — Lean-free cut prototype `Raw → Raw → Raw`.

### Tower (ℕ-pair / ℕ-triple → other number systems via quotient)

  - `Tower/NatPairToInt.lean`      — ℤ via additive diagonal quotient.
  - `Tower/NatPairToQPos.lean`     — ℚ₊ via multiplicative quotient.
  - `Tower/NatTripleToZ2.lean`     — ℤ² via 3-axis projection.
  - `Tower/PairCompletion.lean`    — the invert move, once.
  - `Tower/PairCompletionUniversal.lean` — the invert move is THE universal
                                     group completion.

## Top-level

  - `Lens/Number/Nat213.lean` aggregator.

## Where to add new files

  - New representation             → `Nat213/<Name>.lean`
  - New theorem over `Nat213`      → extend the relevant discipline file
  - Bridge between representations → extend `Bridge.lean`
  - Tower construction (Int/Rat/…) → `Tower/<Type>.lean`

## Discipline

All theorems ∅-axiom (verified via `tools/scan_axioms.py` / `#print axioms`).
</content>
</invoke>
