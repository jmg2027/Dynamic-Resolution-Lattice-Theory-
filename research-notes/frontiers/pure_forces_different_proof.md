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

### B — Fermat's two-square theorem, hard direction, via Thue (★★ capstone B-case)
`NumberTheory/TwoSquareTheorem`. Every prime `p ≡ 1 (mod 4)` is a sum of two
squares: `two_square : ∃ a b : Nat, p = a*a + b*b` (and the `isSumTwoSq` form).
This was the "Next target" predicted below — and it closed **in full** (19 PURE,
no fallback), the descent to `a²+b² = p` included. The classical proof is Thue's
lemma (a `⌊√p⌋`-box pigeonhole giving a small `(a,b)` with `a ≡ x·b (mod p)`) plus
a minimal-counterexample / size descent — both non-constructive (LEM +
well-ordering + a pigeonhole `∃` with no extraction). ∅-axiom forces all of it to
*compute*: `QRNegOne` gives the `x` with `p ∣ x²+1`; the **new
`Pigeonhole.exists_collision_lt`** produces the actual colliding box pair from
`Fin (q²) → Fin p` (`q = isqrt p + 1`, `q² > p`); the witness `(a,b)` is read off
by `i ↦ (i/q, i%q)` and signed differences; the modular core
`dvd_sq_sum` (`p∣X²+1 → p∣A+XB → p∣A²+B²`, via the Brahmagupta identity
`A²+B² = (A−XB)(A+XB) + B²(X²+1)`) gives `p ∣ a²+b²`; and the classical "positive
multiple of `p` below `2p` must be `p`" size argument is a literal computation
(`eq_p_of_dvd_lt_two_mul`, with `isqrt_sq_lt_of_prime` — a prime is not a perfect
square — giving the strict `a²+b² ≤ 2·isqrt²p < 2p`). Reveals: **the two-square
witness `(a,b)` is an algorithm output — the box collision is produced, the
descent is a bounded computation — not an abstract existential.** This is the
deepest demonstration so far that `exists_collision` is the right primitive: a
whole classical theorem's non-constructive content localizes to "produce the
pigeonhole pair." (19 PURE; reuses `QRNegOne`, `exists_collision_lt`, `IntSqrt`,
`PolyRoot` Nat↔Int dvd bridges, `Int213`/`ring_intZ`.)

### B — `x⁴ + y⁴ = z²` has no positive solution, by *constructive* descent (★★ capstone B-case)
`NumberTheory/FermatQuartic`. `no_quartic_sq : ∀ x y z, 0<x → 0<y → x⁴+y⁴ ≠ z²`
(and `no_quartic_quartic : … ≠ z⁴`). This was the "Next target" — and like the
two-square capstone it closed **in full** (29 PURE), descent included. The
textbook proof is the **archetypal minimal-counterexample**: assume a solution
with least `z` (well-ordering + LEM), derive a smaller one, contradict
minimality. ∅-axiom has no well-ordering *as a proof device*, so the descent
becomes an **explicit terminating recursion** — `Nat.strongRecOn` on `z` — where
the inductive step does not *assume* a minimal witness but **constructs** the
strictly-smaller solution `(a,b,c)` as a computed function of `(x,y,z)`: two
applications of a Pythagorean-triple converse (`pyth_converse`, ~90 lines — *not
in the corpus before*, built here) plus the coprime-square split
(`SquareCharacterization.coprime_isSquare_mul`, the gcd-route square root) which
literally *returns* `a = √r`, `b = √s`, `c = √(r²+s²)` with `c ≤ m² < z`. Reveals:
**"no solution" is not "minimality contradicted" but "the strictly-`z`-decreasing
constructor `descent_step` cannot keep terminating" — well-founded recursion does
the work the well-ordering axiom did classically; the descent *map* is the
content, each smaller leg an explicit gcd-computed number.** Whole proof is
Nat-native (no signed integers). (29 PURE; reuses `SquareCharacterization`,
`CoprimeMultiplicative`, `Gcd213`, `Valuation`/`vp`.)

### B — infinitely many primes `≡ 3 (mod 4)`, by a *computed* Euclid witness (★ clean B-case)
`NumberTheory/PrimesThreeModFour`. `infinitely_many_primes_3mod4 : ∀ N, ∃ p,
N < p ∧ IsPrime213 p ∧ p%4=3` (the cofinal form — "infinitely many" with the
prime *exhibited above any bound*). The classical proof posits a **finite
exhaustive list** `p₁,…,p_k` of all such primes, forms a number, and derives a
contradiction (LEM + a finiteness assumption). ∅-axiom drops both: given any `N`
it **constructs** `M = 4·N! − 1` (so `M ≡ 3 mod 4`) and runs the factorization
search to *compute* a prime `q ≡ 3 mod 4` with `q > N`. Keystone
`exists_prime_factor_3mod4 : m%4=3 → ∃ q, prime q ∧ q∣m ∧ q%4=3` by strong
induction (`Nat.strongRecOn`) on `m`: `q = minFac m` is prime and odd (m odd), so
`q%4 ∈ {1,3}`; if `3` it is the witness, if `1` then `m/q ≡ 3 mod 4` and `< m`,
recurse. The `q ≤ N` case is refuted by `q ∣ N! ⟹ q ∣ 4·N! = M+1`, so with `q∣M`,
`q ∣ 1` (using `−1` not `+3` to dodge the `q=3` leak). Reveals: **the new prime
is an algorithm output (the least `≡3 mod4` prime factor of `4·N!−1`), certified
by the keystone — not a prime extracted from a refuted minimal counterexample;
the obstruction "`≡3 mod4` ⟹ has a `≡3 mod4` prime factor" is itself a computed
factor.** (14 PURE; reuses `PrimeFactorization.minFac`, `VpMul.IsPrime213`,
`Gcd213.dvd_sub_213`. New pure-twin finds: `Nat.mul_assoc` and
`Nat.mod_mod_of_dvd` both carry `propext` → `PureNat.mul_assoc` /
`AddMod213.mod_mod_of_dvd`.)

### B — Erdős–Szekeres, monotone subsequence via the label box (★ fresh-domain B-case)
`Combinatorics/ErdosSzekeres`. Any sequence of `> (r−1)(s−1)` distinct values has a
strictly-increasing subsequence of length `r` or a strictly-decreasing one of
length `s`: `erdos_szekeres : (r−1)*(s−1) < n → (∀ i j, i≠j → a i ≠ a j) →
(∃ i, r ≤ incVal a i) ∨ (∃ i, s ≤ decVal a i)`, with the **explicit subsequence
extracted** (`inc_subseq` returns a strictly-monotone `Fin r → Fin n` with `a`
increasing along it). Classical Erdős–Szekeres is an abstract pigeonhole `∃` (two
indices share an `(inc,dec)` label) wrapped in `by_contra`. ∅-axiom forces the
colliding pair to be **computed**: the label map `g : Fin n → Fin ((r−1)(s−1))`
packs `(inc−1)(s−1)+(dec−1)`, `exists_collision_lt` *returns* the actual `i≠j`
with `g i = g j`, and the strict-order step (`a i < a j ⟹ inc i < inc j`) makes
equal labels with `i<j` impossible — the box overflows. The outer `Or` is a
constructive bounded search (`scanBox`, mirroring `Pigeonhole.scan`) over `Fin n`
with `Nat.decLt` — no `by_contra` on a non-decidable `∃`. The subsequence
extraction is **choice-free**: `incPredData` returns the argmax index *as data*
(`PSigma`/`Sum`), so iterating the predecessor chain needs no `Classical.choice`.
Reveals: **the monotone-run witness is an algorithm output — the `inc`/`dec`
strong recursion + the computed collision + the data-returning argmax — not an
abstract pigeonhole existential.** A third reuse of `exists_collision`, in a fresh
domain (sequence/order combinatorics, broadening beyond number theory). (29 PURE;
reuses `Pigeonhole.exists_collision_lt`, `EncodePair213` decoder, `Max213`.)

### A — Euler's totient is multiplicative, by the explicit CRT counting bijection (★ closes the leg's own loop)
`NumberTheory/TotientMultiplicative`. `totient_mul : gcd213 m n = 1 → totient(m*n)
= totient m * totient n` (m,n > 0). Classically a corollary of the **CRT ring
iso** `ℤ/mn ≅ ℤ/m × ℤ/n` (units ↦ unit-pairs), riding on `Quot.sound`. With no
quotient ring, ∅-axiom forces the explicit **counting bijection**: `x ↦ (x%m,
x%n)` is a bijection `[0,mn) ↔ [0,m)×[0,n)` (the corpus `CRTReconstruction`), and
`gcd(x,mn)=1 ⟺ gcd(x,m)=1 ∧ gcd(x,n)=1` (coprime m,n) splits the coprimality
indicator as a product (`coprimeInd_mul_split`), so the totient sum reindexes
(`weighted_partition_by_key` + `sumTo_reshape`, the `rkey x = (x%m)·n + x%n`
fiber) and factors (`sum_mul_sum`) into `totient m · totient n`. Reveals: **the
CRT iso is the reconstruction algorithm; φ multiplicative is the Fubini reindex
of the coprimality-indicator sum, computed — not a quotient-ring corollary.**
Notably this **closes the leg's own loop**: it is proved on `UnitsOfZn`'s gcd
mod-invariance + `CRTReconstruction`'s bijection — two vein-A results built
earlier this same session — demonstrating the representative-level infrastructure
compounds. (20 PURE; reuses `EulerTotient.{totient,coprimeInd}`,
`CRTReconstruction`, `CoprimeMultiplicative`, `DivisorProductReindex`.)

## Vein C — analysis: the modulus is forced, or the import is named and measured

The user's challenge ("do continuity / limits / analysis — the things that *look*
impossible ∅-axiom"). Analysis splits cleanly: theorems that ARE ∅-axiom once the
**modulus** classical analysis hides is supplied (the corpus's native mode), and
theorems that genuinely require an **omniscience principle** — for which the
honest ∅-axiom result is the *calibration* implication (the principle is a
hypothesis, not an axiom), placing the theorem on the reverse-math ledger.

### C — Bolzano–Weierstrass calibrated to LPO (★ "name and measure the import")
`Logic/BolzanoWeierstrass`. Binary BW: every `{0,1}`-sequence has a convergent
(eventually-constant-valued) subsequence (`HasConstSubseq`). This is **not** an
unconditional ∅-axiom theorem — and saying so plainly is the no-exterior guard in
action (no internal handle, so name the import). The honest content is the
calibration, all PURE (the omniscience principle is a hypothesis variable):
`lpo_of_bw : (∀ a, HasConstSubseq a) → LPO` (binary BW ⟹ LPO, the **strongest**
base rung — via feeding BW the monotone prefix-OR stream, whose subsequence value
decides `f`); the constructive cores `subseq_of_unbounded_true` /
`subseq_of_eventually_false` (fully ∅-axiom *once the witness is supplied as
data*); and `lpo_decides_const_false_or_some_true` (LPO settles only the trivial
Σ⁰₁ dichotomy). Sharp finding: `bw_of_lpo` at **plain LPO is not provable** —
extracting the subsequence needs deciding "`true` occurs unboundedly often"
(Π⁰₂), strictly above the ledger's LPO. So BW is pinned at **≥ LPO** with forward
content at Σ⁰₂. Reveals: **classical BW's choice/LEM is not removable — it is the
residue's refused "freeze a transition into a verdict" move, here *named* (LPO)
and *measured* (Π⁰₂); the calibration implication is the ∅-axiom theorem.**
(13 PURE; reuses `Logic.Omniscience`, `Logic.Pi01Decision`.)

### C — Extreme Value Theorem, modulus form: max value computable + approached, maximizer reached by none (★★ analysis capstone)
`Analysis/ExtremeValue`. Classical EVT *attains* the max at a point — needs LEM to
locate it. ∅-axiom forces the honest form, unconditionally PURE. Over a
modulus-continuous `f` on the dyadic grid of `[0,1]` (`structure ModContOnGrid`:
grid values + uniform-continuity modulus `omega`), the supremum **value** `Msup f`
is a genuinely **computable real** — the corpus `CauchyCutSeq.limit` with a
convergence modulus `supN` derived from `omega` — and the headline `evt_sup`
bundles: (i) `Msup` is *located/approached* (`sup_approached`: realized exactly by
a computed finite-resolution grid-max past `supN`), (ii) `Msup` *bounds* `f` on the
grid with a convergence modulus (`fval_le_Msup`), (iii) the max is *attained at
every finite resolution* (`gridMax_attained`, the finite list-max `cutEq` a
computed grid point). The forcing point `max_reached_by_none`: that finite argmax
**moves with the resolution** — nothing constructs a single dyadic `x*` with
`f x* = Msup`; the maximizer is the `n→∞` limit, **reached by none** — the
analysis-level `object1_not_surjective`. Non-vacuous: `constModCont` (the constant
function is a `ModContOnGrid`). Reveals: **the modulus `supN`/`omega`, not a
maximizing point, is the entire computable content classical EVT hides; the
supremum is located but attained by no pointing — limits reached by none
(`the_form_of_the_residue.md`).** (23 PURE; reuses `Real213/Core/CutPoset`,
`Real213/Lattice/CutMaxMin`, `Analysis/CauchyComplete.CauchyCutSeq`.)

The pair calibrates the whole analysis challenge: **EVT** is unconditionally
∅-axiom once the modulus is supplied (the modulus *is* the theorem); **BW** genuinely
needs an omniscience principle, so the ∅-axiom result is the *calibration*
(`BW ⟹ LPO`, Π⁰₂ forward). Together: where classical analysis reaches for an axiom,
213 either forces the hidden modulus or names and measures the import — never
smuggles an exterior.

### C — Heine–Cantor calibrated against the fan theorem (★ ledger entry, dual to WKL)
`Logic/HeineCantor`. "A pointwise-continuous function on the compact `[0,1]` is
uniformly continuous" — classically by compactness; constructively *exactly* the
**fan theorem** (a Brouwerian/bar-induction principle). The ∅-axiom result is the
calibration `heineCantor_of_fan : (∀ m, FanTheorem (precTree f m)) →
PointwiseContinuous f → UniformlyContinuous f`, bracketed by the two ∅-axiom
halves: `bar_of_pointwiseCont` (pointwise continuity ⟹ the precision tree
`precTree f m` is a `Bar` — every point/path is eventually pinned to `1/2^m`) and
`uniform_of_bounded` (a uniform depth `Bounded` ⟹ a uniform modulus). The fan
theorem is **load-bearing, not decorative**: `UniformlyContinuous` needs one depth
valid for *all* addresses at once, `PointwiseContinuous` gives only a per-point
depth, and the sole bridge `Bar → Bounded` IS `FanTheorem`. Reuses the corpus
`Logic/WKLHeineBorel.{Bar,Bounded,FanTheorem,takePrefix}` verbatim — everything
stays `Bool`/`List` (decidable), which is what keeps it ∅-axiom (no `Cut` ε-δ
existentials). Reveals: **HC's classical compactness of `[0,1]` is named and
measured as the fan theorem; the calibration is the theorem.** Adds HC to the
reverse-math ledger at the fan rung, dual to `wkl_heineBorel_calibration`'s WKL
rung. (10 PURE.)

### C — uniform limit of continuous functions is continuous, modulus computed (★ unconditional)
`Analysis/UniformLimitContinuous`. Classically the "3ε" theorem, stated `∀ε∃δ`
with `δ` left unspecified. ∅-axiom forces the content open: `uniform_limit_continuous`
takes `F n` each continuous with modulus `ω_ n` and `F → f` uniformly with rate
`r`, and concludes `f` is continuous with the **explicitly computed** modulus
`Ω m = ω_{r(m+2)}(m+2)` — borrowing one index's modulus at the index the
convergence rate delivers, sharpened to scale `m+2` so the three error pieces
(two convergence gaps + one inner continuity gap), each `< 1/2^(m+2)`, sum to
`< 1/2^m` via the quarter-triangle `qtri`. No compactness, no omniscience, no
LPO/fan — the convergence rate `r` plus one `f_n`'s modulus *are* the new modulus.
Abstract over any `1/2^m`-graduated metric (`structure MetricModulus`), with a
concrete `distMet`/`Nat`-distance instance + `inhabited_uniform_limit` (the `id`
sequence) proving it non-vacuous. Reveals: **the limit's continuity modulus is not
asserted to exist — it is computed from the data; the modulus is the theorem.**
The "force the modulus" half, companion to the BW/HC calibrations. (20 PURE.)

### C — Dini's theorem calibrated against the fan theorem (★ fan rung, sibling of Heine–Cantor)
`Logic/Dini`. A *monotone* sequence of continuous functions converging *pointwise*
to a continuous limit on `[0,1]` converges *uniformly* (Dini) — classically by
compactness, constructively *exactly* the fan theorem. `dini_of_fan : (∀ m,
FanTheorem (diniTree F f m)) → MonoConv F f → PointwiseConv F f → UniformConvStable
F f`, bracketed by the two ∅-axiom halves `bar_of_pointwiseConv` (monotone
pointwise convergence ⟹ the Dini precision tree is a `Bar`) and `uniform_of_bounded`
(`Bounded` ⟹ a uniform converging depth over the fan). The genuinely-new ingredient
vs Heine–Cantor is **monotonicity**: `uniformStable_of_bounded_mono` is where
`MonoConv` turns the per-interval converged depth into a convergence index valid
for *all larger indices* (the substance of Dini); without it only the plain per-fan
bound `dini_of_fan_plain` holds. Mirrors `HeineCantor`'s decidable `Bool`/`List`
style (no `Cut` ε-δ), reuses `WKLHeineBorel.{Bar,Bounded,FanTheorem,takePrefix}`
verbatim. Reveals: **Dini's compactness is named as the fan theorem; monotonicity
is what makes the bar's per-interval bound a uniform convergence index.** (14 PURE.)

### C — the real sign-dichotomy IS LLPO: why exact IVT/bisection can't be ∅-axiom (★★ analytic-LLPO calibration, two-sided)
`Logic/RealDichotomyLLPO`. The canonical constructive-analysis calibration:
`RealDichotomy := ∀ x : Cut, cutLe x one ∨ cutLe one x` (the sign decision) is
**equivalent to LLPO** — `llpo_of_realDichotomy : RealDichotomy → LLPO` and the
converse `encodedDichotomy_of_llpo : LLPO → ∀ f (at-most-one), cutLe (yf f) one ∨
cutLe one (yf f)`. The encoding: from an at-most-one-true `f`, build the cut `yf f`
= `1 ± 2^{-(n+1)}` (positive sign if the unique fire is at an even index, negative
if odd; `1` if `f` never fires — shifted by `+1` since corpus cuts are
non-negative). Its sign decides the even/odd LLPO disjunction: `cutLe (yf f) one ⟹
∀k, f(2k)=false` (`noEvenFire_of_le`), `cutLe one (yf f) ⟹ ∀k, f(2k+1)=false`
(`noOddFire_of_ge`). The odd sign lemma needs a fine separating probe (denominator
`~2^{n+1}` to fit `2^{-(n+1)}` between `yf f` and `1`) — **that denominator
blow-up is the omniscience cost made visible**. Reveals: **the corpus real is a
sign-undecided cut; deciding `x ≤ 0 ∨ 0 ≤ x` for the encoded real IS LLPO, so the
*exact* IVT / bisection's "is `f(mid) ≤ 0` or `≥ 0`?" step cannot be ∅-axiom — and
the corpus's *approximate* IVT (`RootCertificate`, `cutEq … 0`) stays ∅-axiom
precisely because it never makes the global sign verdict, only `cutEq` at a
tolerance.** The deepest analysis calibration: it locates exactly why the corpus
does analysis approximately. (31 PURE; reuses `cutLe`/`constCut`, `Logic/LLPO`.)

### C — Banach fixed-point theorem, geometric modulus computed (★ force-the-modulus, reuses our own MetricModulus)
`Analysis/BanachFixedPoint`. Classically a contraction on a *complete* metric space
has a unique fixed point — via completeness as an *existence* axiom. ∅-axiom forces
it computed: the Picard iterates `xₙ = Tⁿx₀` are Cauchy with an **explicit
geometric modulus**, and the fixed point is their Cauchy limit, approached by every
iterate but reached by none (the `ExtremeValue` residue picture). `Contraction M T`
= `T` advances the dyadic scale one level (`close (m+1) x y → close (m+2) (Tx)(Ty)`,
ratio ≤ 1/2); `picard_step_geometric` (n-th gap at scale `s+1+n`) → `picard_tail`
(the `Σ1/2^k` tail bounded *uniformly in reach j*) → ★ `picard_cauchy` with the
**computed modulus `N(m) = m`** (no omniscience). Over a `CompleteMetricModulus`
(completeness as *data + spec* `lim` + `climconv`, not an existence miracle),
`banach_fixed_point : ∀ m, close m x* (T x*)` (located equality `T x*=x*` to every
scale) and `banach_unique` (two exact fixed points in a ball are `close m` for every
m — the contraction halves their gap with no padding). Non-vacuous (`trivComplete`
instance). Reveals: **the fixed point's existence is not a completeness miracle —
the geometric convergence modulus is computed from the ratio + first step; the
fixed point is the explicit Cauchy limit, approached not attained.** Reuses this
session's own `UniformLimitContinuous.MetricModulus`/`ctri`/`qtri` — the metric
infrastructure compounds. (12 PURE + namespaced headlines verified.)

### C — the real-decision triad: equality ⟺ WLPO, apartness ⟺ MP (★★ completes sign/equality/apartness ↔ LLPO/WLPO/MP)
`Logic/RealEqualityWLPO` + `Logic/RealApartnessMP`. With `RealDichotomyLLPO` (sign
⟺ LLPO) these complete the canonical Bishop triad: the **three basic decisions
about a real each cost a precisely-named omniscience principle**, mirroring the
corpus `lpo_iff_wlpo_and_mp` (LPO = WLPO ∧ MP) at the real-number level.
- **equality ⟺ WLPO** (`RealEqualityWLPO`, 16 PURE, two-sided): deciding whether a
  real *is* zero is WLPO. Encode `xf f = Σ[f n]/2^(n+1)` (non-negative); `cutEq
  (xf f) zero ⟺ ∀n, f n = false` (`xf_eq_zero_iff`), so `cutEq x 0 ∨ ¬cutEq x 0`
  IS WLPO (`wlpo_of_realEqDecision` + converse). A single fire lifts the sum
  `≥ 1/2^(n+1)`, detected at resolution `k=n+1`.
- **apartness ⟺ MP** (`RealApartnessMP`, 15 PURE, two-sided): a non-zero real
  being *apart* from zero (a located positive distance `Apart x := ∃ k, x 0 (k+1)
  = false`) is Markov's principle. `¬ cutEq (xf f) zero` is purely **negational**
  (a pointwise case-split, extracting no Nat); the apartness hypothesis upgrades it
  to a *located* resolution where `xf f` reads strictly above 0, and that bound
  makes the fire-search **bounded** (`fire_of_Q_pos`, a decidable scan) — turning
  "not-everywhere-false" into "∃ explicit witness", exactly MP
  (`mp_of_realApartness` + converse `realApartness_of_mp`). Sharp constructive
  insight: the naive `∃N, x ≥ 1/2^N` apartness is *genuinely false* for partial-sum
  cuts (coarse approximants can't see the fire yet), so the cut-bit witness form is
  forced — the located bound is what makes the otherwise-unbounded search terminate.

Reveals: **the residue's reals are decision-undecided cuts; sign / equality /
apartness are three distinct verdicts, each = LLPO / WLPO / MP — a complete map of
where constructive analysis's real-number decisions sit on the omniscience ledger.
The negation (`¬cutEq`) is free; locating the witness (apartness) is MP; the
disjunctive verdict (sign/equality) is LLPO/WLPO.** Both reuse the
`RealDichotomyLLPO` cut-encoding — infrastructure compounding.

## Forward hunt (targets selected by the criterion)

- **A**: a theorem classically a *quotient-ring isomorphism* (CRT `ℤ/mn ≅
  ℤ/m × ℤ/n`, or a first-iso instance) re-proven as an **explicit reconstruction
  bijection** on representatives — reveals the iso *is* an algorithm. (Check
  `ModArith/LensCRT` for overlap first.)
- **B**: classical results whose only textbook proof is minimal-counterexample
  — and whose descent witness is interesting (not just "a factor exists").
  - ~~**Next target:** every prime `p ≡ 1 (mod 4)` is a sum of two squares.~~
    **DONE** — `NumberTheory/TwoSquareTheorem`, 19 PURE (see the capstone B-case
    above). The whole non-constructive content localized to
    `exists_collision_lt`, exactly as predicted.
  - ~~**Next target:** `x⁴+y⁴=z²` has no positive solution (Fermat descent).~~
    **DONE** — `NumberTheory/FermatQuartic`, 29 PURE (capstone B-case above). The
    descent became an explicit `Nat.strongRecOn` constructor, exactly as
    predicted; also built the missing `pyth_converse`.
  - ~~**Selected:** infinitely many primes `≡ 3 (mod 4)`.~~ **DONE** —
    `NumberTheory/PrimesThreeModFour`, 14 PURE (clean B-case above).
  - **Rejected (honest, duplicate result):** `√2`/`√p` irrationality by
    v2-parity. The bare impossibility `m² ≠ 2k²` (and `3,5`) is already PURE in
    `NumberSystems/Irrational/SqrtPure` and `Sqrt2KernelFree` — via the *descent*
    route (`DescentBase`/`descent_step`/`m_even_of_sq`). A v2-parity reproof
    would be a *different proof of an already-proven theorem*, not a case where
    ∅-axiom forces the new shape — both routes are ∅-axiom. Not collected.
  - **Unselected candidates:** (A) the First Isomorphism Theorem for a concrete
    `ℤ → ℤ/n` reduction, as an explicit section/retraction on representatives;
    (B) Dirichlet's approximation theorem `∀ α N, ∃ p q, q≤N, |qα−p|<1/N` via the
    box pigeonhole (`exists_collision` on `N+1` fractional parts → `N` boxes) —
    reuses the new primitive over `Real213`, witness `(p,q)` computed. Pick by
    sharpness of the revealed constructor.
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
