# `Lens/Number/Nat213/` — 213-native positive naturals + the descent-leg discipline

ℕ₊ as readings of `Raw`'s distinguishing spine, plus an elementary number theory
(divisibility → primes → FTA → infinitude → Chebyshev) computed **entirely over the
Raw-generated `Nat213`** — the **descent leg** made concrete (narrative:
`theory/math/numbersystems/naturals_from_the_spine.md`,
`theory/essays/foundations/raw_and_lens_explained.md`).

## Files (32 + Tower/5)

### Representations

  - `Raw.lean`             — Method A Raw chart (canonical).
                             `one := Raw.a`, `succ n := slashOrSelf n Raw.b`,
                             `numeral : Nat → Raw`, `value : Raw → Nat`.
                             **Chart structure only — no Raw-side arithmetic**
                             (Option C); arithmetic lives on `Nat`/`Peano`.
  - `Peano.lean`           — Inductive `Nat213 | one | succ` with its own
                             arithmetic (`add`/`mul`/`pow`/`powNat`/`factorial`, no-zero/no-
                             subtraction shape *forced* by the primitive;
                             `pow_add`/`pow_mul`/`mul_pow`; `powNat` = the
                             `Nat`-exponent power with `powNat a 0 = one`).  The
                             carrier the descent-leg discipline is computed over.
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
                             + power (`pow_lt_pow_base`) monotonicity, native
                             cancellation, square-injectivity (`mul_self_inj`).
                             No Lean `Nat` order, no `toNat`.
  - `Divisibility.lean`    — `Dvd` over `Nat213`'s own `mul`: a partial order with
                             bottom `one`, no top (`dvd_antisymm`, `dvd_no_top`);
                             refines `le` (`dvd_imp_le`); power facts
                             (`dvd_pow_self`, `pow_dvd_pow`).
  - `Irreducible.lean`     — irreducibility over the Raw-generated ℕ₊.
  - `EuclidUnique.lean`    — Euclid's lemma (`euclid`) over `Nat213`; subtractive
                             gcd existence + multiplicative spec (`gcd_exists_mul`).
  - `Gcd.lean`             — the gcd discipline (`IsGcd`): divisibility is a
                             meet-semilattice — gcd exists + unique + multiplicative
                             law `gcd(c·a,c·b)=c·gcd(a,b)`; reads out as a native gcd
                             (`isGcd_toNat` spec-level, `isGcd_toNat_eq` value-level =
                             `gcdW`). Extracted from `gcd_exists_mul`.
  - `Coprime.lean`         — coprimality (`Coprime a b := IsGcd a b one`): Euclid's
                             coprime-division law `coprime_dvd_mul`, descent to
                             divisors, multiplicative closure (`coprime_mul`),
                             power closure (`coprime_pow`), coprime factors multiply
                             (`coprime_mul_dvd`), Bézout in readout form
                             (`coprime_bezout`), the Prime↔Coprime bridge
                             (`irreducible_coprime_iff`). Built on `Gcd`.
  - `ToNatReadout.lean`    — the depth readout `toNat` is a faithful ordered-semiring
                             embedding onto ℕ₊: `lt`/`le`/`Dvd` read as their native
                             counterparts (`{lt,le,dvd}_toNat_iff`), surjective
                             (`toNat_surj`), `toNat_powNat`, capstone `toNat_faithful`.
  - `WellOrder.lean`       — well-foundedness as a named API: `strong_induction`
                             (named `wf_lt.induction`) + `well_ordering` (every
                             inhabited decidable predicate has a `lt`-minimal
                             witness, constructive via `decBoundedExists`).
  - `Congruence.lean`      — modular arithmetic: `ModEq m a b := ∃ k l, a+m·k=b+m·l`
                             (subtraction-free, no zero needed) is a congruence on the
                             semiring (`modeq_congruence`); modular exponentiation
                             (`pow_compat`), the defining step (`modeq_add_mul`), and
                             the readout iff into native ℕ (`modeq_toNat_iff`); the
                             Chinese Remainder Theorem (`crt_iff`, both ways, via
                             `modeq_cases` + `coprime_mul_dvd`); modulus monotonicity;
                             coprime-factor cancellation (`modeq_cancel_coprime`).
  - `Valuation.lean`       — `p`-adic structure: (A) `vp` (multiplicity read OUT
                             into ℕ via `Peano.powNat`; `pow_vp_dvd`; exactness
                             `le_vp_iff`); (B) `padic_factorization` + uniqueness
                             (native `n=p^k·m`, `¬p∣m`, for `p∣n`); the carrier
                             weld `vp_eq_vpSub` (`vp p n = vpSub p.toNat n.toNat`,
                             the generated valuation = native `subMod` `vpSub` of
                             the readouts, via `dvd_toNat_iff` + `toNat_powNat`).
  - `ModArithReadout.lean` — *transport, not re-derivation*: the native-ℕ modular
                             corpus (`Lib/.../ModArith`) inherited along `toNat`.
                             `mod_eq_imp_additive` bridges the native `%`-form to the
                             additive form `modeq_toNat_iff` speaks; `modeq_of_toNat_mod`
                             packages the transport functor; **Fermat's little theorem**
                             (`flt_primary` `a^p≡a`, `flt_main` `a^(p-1)≡1`) and
                             **Wilson's theorem** (`wilson` `(p-1)!≡p-1`, via `toNat_factorial`)
                             over `Nat213`, one-line corollaries of native
                             `universal_flt_*` / `WilsonTheorem.wilson`.
  - `Prime.lean`           — irreducible ⟺ prime (`irreducible_iff_prime`), the
                             UFD-defining coincidence; a prime dividing a power
                             divides the base (`irreducible_dvd_pow_iff`).
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
