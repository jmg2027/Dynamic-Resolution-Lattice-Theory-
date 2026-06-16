# When ∅-axiom forces a different proof (collection)

A running collection, per the originator's criterion: not "classical theorem,
PURE proof" (which is usually `(standard proof) − (axiom import)` =
bookkeeping), but **theorems where requiring ∅-axiom forces a *structurally
different* proof — and the difference reveals something** (an explicit
witness / algorithm / representative-level operation the classical proof hid).

The discriminator (a case only counts if BOTH hold):
1. the standard textbook proof uses a non-constructive / quotient / impredicative
   principle in a **load-bearing** way (not just because the ambient library is
   built on it), AND
2. the ∅-axiom route is **not** the same proof with lemmas swapped — its shape
   changes, and the new shape exposes constructive content.

Excluded (the bookkeeping kind, deliberately not collected): swapping
`Nat.dvd_trans`→`dvd_trans_213`, `rw`-on-`Iff`→`.mp/.mpr`, `funext`→pointwise,
`Nat.mul_mod_left`→`NatDiv213.…`. Real but not revealing.

## Three veins of genuine forcing

- **A — Quot.sound avoidance.** Theorem classically stated on a *quotient*
  (ℤ = ℕ² quotient, ℚ = pair quotient, ℤ/n, group quotients), proven on
  *representatives*. Reveals: the quotient was packaging; the operation lived
  on the representative all along ("the tuple IS the number",
  `theory/math/numbersystems/slot_arithmetic.md`).
- **B — Classical / LEM avoidance.** An existence theorem classically proved by
  *minimal counterexample / `by_contra`* (LEM + well-ordering), re-proven by
  *explicit descent / bounded search*. Reveals: the witness / algorithm.
- **C — non-effective→effective.** A statement whose classical form is
  non-effective (an existential with no extraction), forced into a *modulus /
  constructor* form. Reveals: the rate / the construction. (The corpus modulus
  programme; `Math/Logic/` omniscience hierarchy is the meta-catalog of exactly
  where classical imports — LLPO/WKL/König/Heine-Borel.)

## Seeded cases (this session) — honest about which genuinely force

### B — Euler's theorem `a^φ(n) ≡ 1 (mod n)` (★ clearest genuine forcing)
`NumberTheory/EulerTheorem`. The natural route — "the order of `a` divides
`φ(n)` (Lagrange), and `a^ord = 1`" — is **circular for composite n**: the
corpus's order theory is prime-specific and "order ∣ φ(n)" for composite n
*needs Euler itself* (it became iter-174 `MultiplicativeOrder`, downstream of
Euler). So ∅-axiom forced the **totative-product permutation** proof: `x ↦ ax`
permutes the units, so `∏(units)` is `LPerm`-invariant ⟹ `a^φ·P ≡ P` ⟹ cancel.
Reveals: Euler is essentially a **permutation-invariance** fact, not a Lagrange
corollary — the group-order packaging hid that for composite moduli.

### B — `exists_nontrivial_factor` (in Wilson's converse)
`ModArith/WilsonConverse`. Classical "least divisor > 1 is prime" is
well-ordering + `by_contra`. The PURE route used `exists_prime_factor`
(bounded search) — the factor is an **explicit, computed** object, not an
abstract minimum.

### B/C — τ-parity & σ-parity via `doubleSum_parity`
`NumberTheory/TauParity`. The textbook "divisors pair `d ↔ n/d`, count mod 2"
becomes, ∅-axiom, the **symmetric double-sum parity** lemma `Σ_{a,b<N} g a b ≡
Σ_a g a a (mod 2)` (off-diagonal pairs cancel). Reveals: the parity is a
**fixed-point count** of the Z/2 involution, computed, not read off a
multiplicativity table. (Partial: the multiplicativity *could* also be
factored; the forcing is in choosing the involution-count form.)

### C — the constructive IVT is the corpus's *native* mode (already pervasive)
Vein C does not need a new entry: `Real213/Bisection/CutBisection` +
`Analysis/DyadicSearch/{DyadicBracket, RootCertificate, MinimalRootLens}` ARE
the constructive intermediate-value theorem. Classical IVT bisects by *deciding*
`f(m) ≷ 0` (LEM on the reals); ∅-axiom forces the **explicit dyadic bracket +
modulus** — the `RootCertificate` is the rate of convergence to the root, and
that rate is the content. The corpus has no classical non-effective IVT to
contrast against because 213 does *all* its analysis modulus-first; vein C is the
default here, not a collectible. (This is itself the point: where classical math
imports LEM for existence, 213 was already constructive.)

### A — Chinese Remainder Theorem as an explicit bijection (★ clean A-case)
`ModArith/CRTReconstruction`. Classical CRT is the quotient-ring iso
`ℤ/mn ≅ ℤ/m × ℤ/n` whose construction rides on `Quot.sound`. With no quotient,
CRT is forced into explicit Nat functions: `crtMap x = (x%m, x%n)` and the Bezout
closed-form `crtSolve`, with `crt_unique` a bare divisibility argument and
`crt_solve_residues` a modular computation; the two round-trips
(`crt_map_solve`, `crt_solve_map`) ARE the bijection. Reveals: **the CRT
isomorphism is literally the reconstruction algorithm `crtSolve`; the quotient
was packaging, the round-trip is the content.** (12 PURE.)

### A — `ℤ/n` is a field ⟺ n prime, on representatives (★ clean A-case)
`ModArith/FieldIffPrime`. Classically a statement about the *quotient ring*
`ℤ/n` (field structure proved by lifting through `Quot.sound`). On
representatives: `isFieldZn n := 1<n ∧ ∀ a, a%n≠0 → hasInverse n a`. Prime ⟹
every nonzero residue has an explicit **Bezout inverse** (`prime_imp_field`);
composite ⟹ an explicit **zero divisor** read straight off the factorization
`(a·b)%n = n%n = 0` (`composite_imp_zero_divisor`, which can't be invertible).
`field_iff_prime` packages it (forward via a constructive `prime_or_composite`
bounded search, no `by_contra`). Reveals: **the field/non-field dichotomy IS
the gcd computation** — invertibility decided by Bezout, failure an explicit
zero divisor; the quotient ring was packaging. (16 PURE.)

### A — cyclic subgroup `⟨a⟩` as the explicit orbit (★ clean A-case)
`NumberTheory/CyclicSubgroupOrbit`. Classically `⟨a⟩` is an abstract cyclic
*subgroup* of the quotient group `(ℤ/n)*`, and `|⟨a⟩| ∣ |(ℤ/n)*|` is Lagrange
via coset counting. With no quotient/abstract group: `⟨a⟩` is the **explicit
finite orbit** `{a^k % n : k < ord}` — distinct below the order
(`pow_inj_below_ord`, via `ord_min` after unit-cancellation), periodic
(`pow_period`), closed under `·` by folding exponents mod `ord`
(`orbit_mul_closed`) — and the divisibility `cyclic_lagrange : ord ∣ φ(n)` is
the **computed** `ord_dvd_of_pow_one` fed by Euler's `a^φ≡1`. Reveals:
**Lagrange's theorem (cyclic case) is the order-divides-totient computation,
not coset counting**; the subgroup is the concrete orbit. (14 PURE.)

### A — subgroups of `(ℤ/n,+)` ↔ divisors of `n` (★ clean A-case)
`NumberTheory/AdditiveSubgroup`. Classically the subgroups of `ℤ/n` are
subgroups of a *quotient group* and "subgroups ↔ divisors" is an abstract
order-iso. On representatives: the additive order of `d` is the **computed**
`n/gcd(d,n)` (`add_order_smul_zero` + `add_order_min`, load-bearing
`n ∣ t·d ↔ (n/gcd) ∣ t`), and each divisor `e∣n` gives the subgroup `⟨e⟩` of
order `n/e` (`subgroup_order`), distinct divisors ↔ distinct subgroups
(`divisor_subgroup_inj`). Reveals: **the subgroup lattice of `ℤ/n` IS the
divisor lattice of `n`, realized by gcd; the quotient group was packaging.**
Honest scope: the full set-equality `⟨d⟩=⟨gcd(d,n)⟩` is given only as the
inclusion direction — the reverse is a *signed* Bezout combination (not
∅-axiom over Nat), so the generator-is-gcd fact is realized at the **order**
level (`subgroup_order`) instead, which is the load-bearing content. (17 PURE.)

### B — every n>1 is a product of primes, by the factorization *algorithm* (★ clean B-case)
`NumberTheory/PrimeFactorization`. Classically the FTA-existence is a
*least-counterexample* proof (well-ordering + LEM: a minimal non-factorable n
is composite, n=ab smaller, both factor by minimality → contradiction). With
no LEM/well-ordering as a proof device, the existence becomes the
**factorization algorithm** `factorize` (reducible fuel recursion: extract the
smallest prime factor, recurse on the strictly-smaller quotient);
`factorize_prod : prodL (factorize n) = n` certifies it, `factorize_all_prime`
gives primality. A sharp extra forcing point: the corpus's *Prop-valued*
`exists_prime_factor` (an `∃`) **cannot be used as data** to build `factorize`
without `Classical.choose` — so a *computable* `minFac` upward search is forced.
Reveals: **the FTA-existence IS the factorization algorithm — the witness is
computed (`factorize 12` reduces to `[2,2,3]` by `decide`), not extracted from
a minimal counterexample**; and a `Prop`-∃ is not data without choice. (16 PURE.)

### A — `(ℤ/n)^×` as the explicit coprime-residue group, on representatives (★ clean A-case)
`NumberTheory/UnitsOfZn`. Classically `(ℤ/n)^×` is the group of **units of the
quotient ring** `ℤ/n` — its very definition presupposes the ring `ℤ/n` and its
unit set, lifted through `Quot.sound`. On representatives over `Nat` there is no
quotient ring: a unit is just a coprime residue `isUnit n a := gcd213 a n = 1`,
and the group structure is read off directly — closure under `·` mod `n` is the
**gcd fact** `gcd(ab,n)=1` (with gcd mod-invariant, `gcd_mod_left`), the identity
is `gcd(1,n)=1`, inverses are **Bezout** (`unit_has_inverse`, the inverse-is-a-unit
half from "any common divisor of `b,n` divides `(a·b)%n = 1`"), and the order is
`φ(n)` — *definitionally* `unit_count_eq_totient : unitCount n = totient n := rfl`,
since the corpus `totient` already counts coprime residues. Reveals: **the
multiplicative group is the explicit coprime-residue set; closure is a gcd fact,
inverses are Bezout, order is φ(n) — the quotient ring was packaging.** (12 PURE.)

### B — divisibility pigeonhole on `[1,2n]`, with a *computed* dividing pair (★ clean B-case)
`NumberTheory/DividesPairPigeonhole`. "Among any `n+1` numbers in `{1,…,2n}`, one
divides another." Classically pigeonhole asserts a **non-constructive `∃`** (two of
the chosen numbers share an odd part — but *which* pair is never exhibited; the
textbook proof is the abstract pigeonhole counting). ∅-axiom forces the explicit
witness in **two** places: (1) the divisibility itself — `same_oddpart_dvd` reads
`a ∣ b ∨ b ∣ a` straight off the **2-adic valuation comparison** (`v2 a ≤ v2 b`
gives the explicit cofactor `2^(v2 b − v2 a)`), not from an abstract "same class";
and (2) the collision — the standard `no_inj_lt` only *refutes* injectivity
(`→ False`), so a `by_cases` on the existential pulled in `Classical`. This forced
a **constructive collision-producing pigeonhole** `Combinatorics/Pigeonhole.exists_collision :
∀ N g, ∃ i j, i ≠ j ∧ g i = g j` (a decidable linear `scan` + `shiftAround`
recursion that *returns* the colliding indices). Reveals: **the dividing pair is
computed — odd-part map collides (the collision is produced, not asserted), then
v2-comparison reads off which divides which — not an abstract pigeonhole `∃`.**
A new reusable primitive (`exists_collision`) fell out: the constructive content of
pigeonhole is the *witness-returning* form. (DP 7 PURE; `exists_collision`/`scan`
2 PURE in Pigeonhole. Two independent agents converged on exactly this shape —
itself evidence the route is forced, not chosen.)

## Forward hunt (targets selected by the criterion)

- **A**: a theorem classically a *quotient-ring isomorphism* (CRT `ℤ/mn ≅
  ℤ/m × ℤ/n`, or a first-iso instance) re-proven as an **explicit reconstruction
  bijection** on representatives — reveals the iso *is* an algorithm. (Check
  `ModArith/LensCRT` for overlap first.)
- **B**: classical results whose only textbook proof is minimal-counterexample
  — and whose descent witness is interesting (not just "a factor exists").
  - **Next target (selected):** every prime `p ≡ 1 (mod 4)` is a sum of two
    squares. The corpus has `QRNegOne` (`∃x, p ∣ x²+1`) and the
    Brahmagupta–Fibonacci multiplicativity (`SumTwoSquares.isSumTwoSq_mul`) but
    **not** the hard direction. Classical proof = Thue's lemma (a pigeonhole over
    a `⌊√p⌋`-box giving a small `(a,b)` with `a ≡ xb`) + descent. ∅-axiom forces
    the **computed** `(a,b)`: the new `Pigeonhole.exists_collision` should supply
    the Thue collision directly, making the two-square witness explicit rather
    than an abstract `∃`. (Reuses `QRNegOne`, `exists_collision`.)
- **C**: a classically-non-effective existence (an "∃ by compactness") whose
  ∅-axiom form needs a modulus, where the modulus is the content.
- **The DIRTY-set test — RESULT (2026-06-16): empty for math.** Scanned the whole
  corpus (`scan_all_axioms.py`): **19607 PURE / 13 real-DIRTY / 36 sealed-by-design**.
  The 36 sealed are the *theses* (`propext` = Prop-as-atom, `Quot.sound` = Lens-
  equality-as-funext). The 13 real-DIRTY are `propext`/`Quot.sound`-only (the same
  thesis surface, not yet prefix-sealed) plus 3 `E213.Tactic.elab*` tactic
  elaborators (`Classical.choice` from Lean's `Elab` monad — metaprogramming
  boundary). **None is a mathematical theorem that is DIRTY because the math needs
  a non-constructive axiom.** Conclusion: the residue already supports every
  *math* result PURELY; the "convert DIRTY math → PURE" vein is exhausted. So
  genuine forcing cases are **forward-only** — new classical theorems whose
  *textbook/Mathlib* proof is non-constructive, re-derived ∅-axiom (the CRT and
  Euler template). This is itself evidence for §7.1: nothing mathematical in the
  corpus needed an exterior import.

## Why this is the better selector
Per `seed/AXIOM/07_primacy.md §7.1`, derivation *confirms* primacy. But a PURE
re-derivation that is mere bookkeeping confirms only that the *library's* axiom
use was incidental — weak evidence. A PURE re-derivation that **forces different
mathematics** is the strong form: it shows the residue reaches the result *by a
route classical math doesn't take*, i.e. the result was always residue-native,
the classical packaging non-essential. Those are the cases worth collecting.

Promotable to `theory/meta/` (a methodology chapter) once ≥ ~5 sharp cases
across ≥ 2 veins are pinned.
