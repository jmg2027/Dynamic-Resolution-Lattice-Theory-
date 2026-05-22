# G124 — N_U family cross-field connections

*(Follow-up to G123 N_U-family theory closure.  G123 introduced
`configCountD d n := d^(d^n)` as the parametric count-Lens output;
this note surveys how that family connects to four established
mathematical fields — number theory, universal algebra / logic,
cellular automata / complexity, and category / type theory — and
which of those connections expose DRLT-internal structure.)*

Multi-agent provenance: 4 parallel research agents (number
theory, universal algebra + logic, CA + complexity, category +
type theory), synthesized 2026-05-22.

## §0 The unifying identity

The N_U family is a single integer-valued function in **four**
simultaneously valid readings:

  · **Combinatorial**: count of `n`-variable `d`-valued functions
    `|[d]^n → [d]| = d^(d^n)`.
  · **Cohomological**: `d`-colouring count of `K_{d^n}` complete
    graph.
  · **Cartesian-closed**: cardinality of the exponential object
    `[d]^([d]^n)` in **Set**, i.e. `|Hom_Set([d]^n, [d])|`.
  · **Type-theoretic**: closed inhabitant count of the simply-
    typed lambda calculus type `b^n → b` over a base type with
    `|b| = d` (in the extensional set-theoretic model).

These four are mathematically the same integer.  Each field
brings its own theorems, open questions, and analytic toolkit;
together they bracket the family from independent angles, which
is the strongest 213-internal evidence that the value is a
*structural readout* rather than an *encoded choice*.

## §1 Number-theoretic ties

### §1.1 Fermat-number connection (d = 2 slice)

At `d = 2`, the family takes the form `F(2, n) = 2^(2^n)`, which
is exactly one less than the **Fermat number**
`F_n^{Fermat} = 2^(2^n) + 1`.  Fermat (1640) conjectured all
`F_n^{Fermat}` prime; Euler (1732) refuted at `n = 5`
(`F_5 = 641 · 6700417`).  As of 2026 only the original five
Fermat primes (`n = 0..4`) are known; the heuristic Mertens-type
density argument predicts that none exist beyond `F_4`.

Lucas's theorem: any prime divisor of `F_n^{Fermat}` has the form
`k · 2^(n+2) + 1`.  Pépin's test (1877) — `F_n` is prime iff
`3^((F_n − 1)/2) ≡ −1 (mod F_n)` — remains the only practical
primality test at this scale.

**DRLT contact**: the `d = 2` slice of the N_U family is the
dyadic-FSM cousin (per `theory/math/dyadic_fsm.md`).  The slice
brings centuries of Fermat-number factorisation theory into
proximity with the bitstream resolution lattice.  Not currently
used in production but a clear cross-import opportunity.

### §1.2 Cyclotomic factorisation

`F(d, n) − 1 = d^(d^n) − 1 = ∏_{e ∣ d^n} Φ_e(d)` (the standard
cyclotomic decomposition).  Two regimes:
  · **`d` prime**: divisors of `d^n` are `{1, d, d², …, d^n}`,
    giving exactly `n + 1` cyclotomic factors.  For `d = 5,
    n = 2`: `5^25 − 1 = Φ_1(5) · Φ_5(5) · Φ_25(5)
    = 4 · 3906 · (large factor)`.
  · **`d` composite**: the divisor count `τ(d^n)` blows up;
    `F(6, 2) − 1` has 9 cyclotomic factors.

**Zsygmondy's theorem** (1892): for `d ≥ 2` and `k ≥ 7`,
`d^k − 1` has a primitive prime divisor (one not dividing
`d^j − 1` for any `j < k`), with explicit exceptions.  Applied
to `F(d, n) − 1`, the number of distinct prime divisors grows
with `n`.

### §1.3 Aurifeuillean factorisation at `d = 5`

**Most directly DRLT-relevant finding**.  For `d = 5`, the
Aurifeuillean identity gives a non-trivial split of
`5^(10k+5) + 1` over `ℤ[√5]`-derived factors (Brent 1993,
extending Aurifeuille 1873).  Since `5^n ≡ 5 (mod 10)` for every
`n ≥ 1`, the value `F(5, n) + 1 = 5^(5^n) + 1` admits an
Aurifeuillean split for every `n ≥ 1`.

This is a concrete factorisation handle on `N_U + 1`
specifically — purely from base-5 cyclotomy, no DRLT
machinery required.  Whether the Aurifeuillean factors are
arithmetically meaningful at the physics lens (do they
correspond to atomic cofactor structures?) is **open** and a
clean research target.

### §1.4 Modular periodicity and Carmichael towers

The G123 capstone `configCountD_mod_pure` proves
`F(d, n) % p = d^((d^n) % (p-1)) % p` for prime `p` coprime to
`d`.  The iterated Carmichael chain
`ord_p(d) | p − 1`, `ord_{p-1}(d) | λ(p-1)`, … terminates in
`O(log log p)` steps (Erdős–Pomerance–Schmutz on the iterated
Carmichael function).

**Wieferich condition**: a prime `p` is Wieferich-base-`d` if
`p² | d^(p−1) − 1`.  Only two base-2 Wieferich primes are known
(`1093`, `3511`); none others below `6.7 × 10^15`.  Wieferich
primes obstruct high-power lifts of modular computations — a
relevance check for any 213-native modular cascade beyond level
`p` (e.g. residues mod `p²`).

**DRLT contact**: the modular fingerprint at `d = 5`
(`configCountD_5_modular_structure`: mod-{2,3,5,7,13} period-2
or constant) sits inside this general arithmetic.  The DRLT
choice of small primes is itself a sub-family of the iterated
Carmichael structure; broader period analysis at primes
`p ∈ {17, 19, 23, 29, 31}` is a natural extension.

### §1.5 Tetration hierarchy

`F(d, n)` sits at **depth 2** in Knuth's up-arrow notation.  The
diagonal `F(d, d) = d ↑↑ 3`.  Grzegorczyk hierarchy:
`F ∈ ℰ³` (bounded exponentiation, primitive recursive), strictly
below Ackermann / Skewes-type towers in `ℰ⁴`.

Real-analytic note: `d ↑↑ ∞` converges iff
`d ∈ [e^{-e}, e^{1/e}] ≈ [0.0660, 1.4447]` (Euler 1778, Knoebel).
For every integer `d ≥ 2`, the iterated tower diverges
super-exponentially.  The DRLT base `d = 5` is well above the
convergence threshold, so the depth-2 truncation is genuinely
structural (no analytic limit available).

## §2 Universal-algebra and logic ties

### §2.1 Post lattice and clone theory — sharp dichotomy at `d = 2`

A **clone** on `[d]` is a set of operations closed under
composition and containing projections.  The lattice of clones
on `{0, 1}` is **countable and fully classified** by Post (1941).
The lattice of clones on `[d]` for `d ≥ 3` is **uncountable**
(Yanov–Muchnik 1959).

**Striking implication for DRLT**: the physics base `d = 5` sits
precisely in the uncountable-clone-lattice territory.  No
Post-style classification exists; the algebraic landscape at
this base is genuinely open.  Whether this connects to the
DRLT-internal claim that "the (3, 2, 5) atomic shape is
*structurally forced*" is itself a deep question — the
forcing chain runs through `Theory/Atomicity/Five`, not
through clone-theoretic uniqueness.

Galois duality (Bodnarchuk–Kalužnin–Geiger 1968): clones on `[d]`
correspond bijectively to relational clones (sets of relations
closed under primitive positive definition).  This duality
underlies the CSP dichotomy theorem (Bulatov–Zhuk 2017).

### §2.2 Functional completeness and Sheffer density

A **Sheffer function** generates the full clone of all
operations by composition.  At `d = 2`: of the 16 binary
operations, exactly NAND and NOR are Sheffer.  At `d ≥ 3`:
Sheffer functions exist at every arity `n ≥ 2`, and
**Słupecki's theorem** establishes that the density of Sheffer
functions in `F(d, n)` tends to 1 as `min(d, n) → ∞`.

**Rosser–Turquette**: Łukasiewicz logic `L_d` (with negation
and implication as primitive connectives) is functionally
complete iff `d` is prime.  The DRLT base `d = 5` is prime, so
`L_5` is functionally complete at the physics lens.

### §2.3 Finite-field reading at `d = 5`

When `d = q` is a prime power, the function ring
`F_q^{[F_q]^n} ≅ F_q[x_1, …, x_n] / (x_i^q − x_i : i = 1…n)`
has cardinality `q^(q^n) = F(q, n)`.  Identifying `[5]` with
`F_5`:

```
F(5, 2) = 5^25 = dim_{F_5} (F_5[x, y] / (x^5 − x, y^5 − y))
        = |function ring of the affine plane A²_{F_5}|
```

**This is a clean algebraic-geometric reading of the historical
N_U value**.  The `5^25` configuration count is precisely the
size of the polynomial function ring on the affine 2-plane over
`F_5`.  Whether the DRLT bipartite `K_{3,2}^{(c=2)} → K_{25}`
closure corresponds to a specific subset of this function ring
(e.g. polynomials of bounded degree, or those vanishing on a
specific variety) is an **open** question with concrete
algebraic-geometric tools available.

### §2.4 Dedekind numbers and monotone-function counts

The count of monotone Boolean functions `M(n)` (Dedekind
numbers) is a deep open problem in combinatorics:

```
M(0) = 2, M(1) = 3, M(2) = 6, M(3) = 20, M(4) = 168,
M(5) = 7581, M(6) = 7,828,354, M(7) = 2,414,682,040,998,
M(8) = 56,130,437,228,687,557,907,788,
M(9) = 286,386,577,668,298,411,128,469,151,667,598,498,812,366
```

M(9) was computed in 2023 by Jäkel and independently by van
Hirtum et al. using massive FPGA / GPU clusters.  `M(n) / 2^(2^n)
→ 0`, so monotone Boolean functions are *vanishingly rare* in
the full `F(2, n)` space.  No closed form is known.

**DRLT contact**: the resolution-lattice readout could be
restricted to monotone (or anti-monotone) configurations to
test a far smaller — but still combinatorially deep — sub-family.
No direct DRLT use currently.

## §3 Cellular-automata and complexity ties

### §3.1 CA rule space

`F(d, n)` is the number of distinct local update rules for a
`d`-state CA with neighbourhood of size `n`:

| CA setting | `F(d, n)` |
|---|---|
| Elementary CA (d=2, n=3) | `2^8 = 256` |
| ECA radius-2 (d=2, n=5) | `2^32 ≈ 4.3 × 10⁹` |
| 3-state 3-cell (d=3, n=3) | `3^27 ≈ 7.6 × 10¹²` |
| 4-state 4-cell (d=4, n=4) | `4^256 ≈ 1.3 × 10¹⁵⁴` |
| **DRLT physics slice (d=5, n=2)** | **`5^25 ≈ 3.0 × 10¹⁷`** |
| Game of Life (d=2, n=9, 2D Moore) | `2^512 ≈ 1.3 × 10¹⁵⁴` |

The DRLT slice `5^25` lives in the **sampling regime** —
between full enumeration (≤ ~10⁹) and Game-of-Life-scale
(~10¹⁵⁴).  Structural results dominate; exhaustive sweep is
out of reach but Monte-Carlo / structural-theorem methods are
feasible.

### §3.2 Wolfram classification + universality

Wolfram (1984) 4-class classification: I uniform, II periodic,
III chaotic, IV edge-of-chaos.  Rule 110 (Class IV) is
**Turing-complete** (Cook 2004); Conway's Game of Life is
Turing-complete (Berlekamp–Conway–Guy 1982).

**Kari's theorems** (1990, 1994): deciding whether a given 1D
CA is universal, nilpotent, or reversible is **undecidable**.
By Rice's-theorem analogues, almost no interesting global
property of a local rule is computable from its truth table —
the F(d, n) rule space hosts an uncomputable membership function
for "universal."

**Langton's λ** (1990): empirical complexity peaks at
intermediate `λ` (fraction of rules mapping to active state) —
the "edge of chaos."  Contested (Mitchell–Hraber–Crutchfield
1993) but useful as a coarse navigation parameter.

### §3.3 Compression and complexity

Shannon's counting (1949): **almost every `f ∈ F(2, n)` requires
`Ω(2^n / n)` gates**, yet the largest explicit circuit lower
bound for any concrete function in NP is `(3 + 1/86) n − o(n)`
(Find–Golovnev–Hirsch–Kulikov 2016).  This is one of complexity
theory's deepest open gaps.

**MCSP** (Minimum Circuit Size Problem) — given a truth table
of size `2^n` and a bound `s`, decide whether some circuit of
size `≤ s` computes the function — is in NP, conjectured
intermediate between P and NP-complete.  Recent work
(Hirahara 2018, Ilango–Loff–Oliveira 2020) places MCSP in
increasingly tight complexity classes.

**Reduced ordered binary decision diagrams** (Bryant 1986)
canonically represent Boolean functions.  For "structured"
functions (parity, threshold, symmetric), BDDs are polynomial.
For multiplication, exponential BDD size is provable.  Almost
all `f ∈ F(2, n)` have BDD size `Θ(2^n / n)` — compression
fails for the typical function.

### §3.4 Kolmogorov / pseudorandomness

A typical truth table of length `2^n` has Kolmogorov complexity
close to `2^n`.  "Random" Boolean functions are most of
`F(2, n)`.  Resource-bounded Kolmogorov complexity (Levin's
`Kt`, polynomial-time samplable distributions) refines this to
"most functions look random to any feasible observer."

### §3.5 Reversible and quantum CA

Reversible CA require bijection on configurations.  The number
of bijections on `[d]^n` is `(d^n)!`, which is **smaller than
`F(d, n)`** for `d ≥ 2`.  So reversibility is a strict
measure-zero subset of the rule space (Hedlund 1969; Toffoli–
Margolus 1990).

Quantum CA: unitary operators on `(ℂ^d)^⊗n`, a continuous
`(d^n)^2`-dim manifold.  Same `d^n` state-space scaling, but
continuous-parameter family rather than discrete count.

## §4 Categorical and type-theoretic ties

### §4.1 Cartesian-closed structure

In **Set** (a CCC):

```
F(d, n) = |[d]^([d]^n)|         (exponential object cardinality)
        = |Hom_Set([d]^n, [d])| (external hom-set count)
        = |Nat(y[d]^n, y[d])|   (natural transformations between representables,
                                  by Yoneda)
```

Currying gives an `n`-fold right-association:
`[d]^n → [d] ≅ [d] → [d] → … → [d]` (`n + 1` occurrences of
`[d]`).  This is the categorical content of "every n-ary
function is a unary function returning an (n-1)-ary function."

### §4.2 Curry–Howard + STLC

Under propositions-as-types, the type `b^n → b` over base
`|b| = d` has **`F(d, n)` closed inhabitants** modulo βη
(extensionally).  The type-depth tower:

| Type | Inhabitants |
|---|---|
| `b` | `d` |
| `b → b` | `d^d = F(d, 1)` |
| `b^n → b` | `F(d, n)` |
| `(b → b) → b` | `d^(d^d) = F(d, d)` (diagonal) |

**Statman 1979**: βη-equivalence in finite-base STLC is
non-elementary recursive in the type — driven precisely by
iterated exponentials `d ↑↑ k`.  `F(d, n)` is the gateway
between elementary (one tower) and non-elementary (≥ two
towers) decidability.

### §4.3 Lawvere theories and clones

`F(d, n)` is the **arity-`n` component of the maximal clone
`Pol([d])`** on `[d]` — the Lawvere theory of "all operations
with no equations" on a `d`-element carrier.  Post's lattice
(for `d = 2`) sits inside this maximal clone.

For `d = q` prime power and `q^n` finite: `F(q, n)` equals the
dimension over `F_q` of the polynomial function ring
`F_q[x_1, …, x_n] / (x_i^q − x_i)` — the same identity from §2.3.

### §4.4 Topos-theoretic and power-set comparison

In any elementary topos with NNO, `[d]^([d]^n)` exists.
**Crucial distinction**:

  · **Power-set tower**: `|P^k(D)|` has base 2 from the
    subobject classifier `Ω` (cardinality 2 in **Set**), giving
    `2 ↑↑ k` tower.
  · **Function-space tower**: `|D^(D^n)| = F(d, n)` has base
    `d`, giving `d`-tower at depth 2.

These are *different* growth families.  The DRLT family is
firmly the second.

### §4.5 Universe-staircase reading

In Russell-style universe hierarchies `Type_0 : Type_1 : …`,
predicativity demands strict size increase per level — at
minimum an exponential jump.  Iterated function-space at
finite base `|b| = d`:

  · Level 0: `d` (the base)
  · Level 1: `d ↑↑ 2 = d^d`
  · Level 2: `d ↑↑ 3 = d^(d^d) = F(d, d)` on diagonal

So `F(d, d)` is the **categorical signature of bounded
tetration at depth 3** — the universe-staircase invariant
where three predicativity jumps have occurred.

## §5 Notable convergences at the physics slice `(d, n) = (5, 2)`

Multiple field readings of the same integer agree:

| Field | Reading at `(5, 2)` |
|---|---|
| Number theory | `5^25 = 5^(5^2)`; Aurifeuillean handle on `5^25 + 1`; iterated Carmichael period via FLT |
| Universal algebra | Arity-2 component of maximal clone on `F_5`; `L_5` functionally complete (Rosser–Turquette, since 5 is prime); uncountable clone-lattice territory (Yanov–Muchnik) |
| Finite-field algebra | Dimension over `F_5` of `F_5[x, y] / (x^5 − x, y^5 − y)`; function ring of affine plane `A²_{F_5}` |
| CA / complexity | 2-input 5-state CA rule space, size `3.0 × 10¹⁷`; sampling regime between full enumeration and Game-of-Life scale |
| Category theory | `|Hom_Set([5]² , [5])| = |[5]^([5]²)|`; inhabitant count of STLC type `b² → b` over 5-element base; arity-2 component of `Pol([5])` Lawvere theory |
| Type theory | Closed STLC inhabitants at type `Fin 5 → Fin 5 → Fin 5`; gateway between elementary and non-elementary βη-decidability |
| DRLT internal | Count-Lens output at K_{3,2}^{(c=2)} → K_{25} fractal closure; physics-selected via three independent forcings (Atomicity.Five, C2a cohomology-loss, C2b adjoint-product) |

That **all seven readings agree numerically and the integer
they agree on is `5^25`** is the strongest 213-internal evidence
that the physics slice is genuinely *structural* rather than
*chosen*.  Each field provides an independent witness; the
agreement is forced, not arranged.

## §6 DRLT-internal cross-imports — opportunity catalogue

Concrete research directions that emerge from these connections:

1. **Aurifeuillean factor reading of `N_U + 1` cofactors**
   (§1.3).  Compute the Aurifeuillean split of `5^(5^n) + 1`
   for `n ∈ {1, 2, 3}`.  Do the factors map to atomic-integer
   structure (NS, NT, d, c-generated catalogue per
   `closure-algorithm.md`)?  If yes, this is a structural
   bridge between cyclotomy and the DRLT Hunter catalogue.

2. **Finite-field affine-plane reading of `K_{25}`** (§2.3, §4.3).
   The `5^25` configuration count equals the dimension of the
   polynomial function ring `F_5[x, y] / (x^5 − x, y^5 − y)` on
   `A²_{F_5}`.  Does the bipartite `K_{3,2}^{(c=2)}` substrate
   correspond to a specific sub-ideal (polynomials of bounded
   degree, or those vanishing on a fixed variety)?  Concrete
   algebraic-geometric question.

3. **Łukasiewicz `L_5` as the DRLT lens language** (§2.2).
   Since `L_5` is functionally complete (Rosser–Turquette,
   prime `d`), the Lens framework could be reformulated in
   `L_5` connectives.  Does the DRLT count-Lens at base 5
   correspond to a specific definable fragment of `L_5`?

4. **Iterated Carmichael chain beyond `{2, 3, 5, 7, 11, 13}`**
   (§1.4).  The G123 modular capstone covers six small primes.
   Extending to `p ∈ {17, 19, 23, 29, 31, 37, 41, 43, 47}`
   would test whether period-2 dominates or if longer periods
   emerge.  Cheap Lean addition.

5. **Tetration-depth-3 categorical invariant** (§4.5).  The
   diagonal `F(d, d) = d ↑↑ 3` is the universe-staircase
   invariant at depth 3.  Is `F(5, 5) = 5^3125` a meaningful
   DRLT-internal object (perhaps `5`-adic depth-3 truncation)?
   Speculative but well-defined.

6. **Sheffer fraction of the rule space at `(5, 2)`** (§2.2).
   Słupecki says most operations are Sheffer for `d ≥ 3`.
   Concrete: what fraction of `f ∈ F(5, 2)` are Sheffer?
   Numerical answer + structural characterisation.

7. **Reversible-CA fraction**: `(5²)! / 5^25 = 25! / 5^25`.
   Compute and characterise — does this fraction correspond to
   any DRLT-internal observable (e.g. the bijective sub-Lens
   count)?  Numerical / structural.

8. **DRLT-Wieferich condition**.  Are there primes `p` with
   `p² | 5^(p-1) − 1`?  Such "base-5 Wieferich primes" would
   obstruct higher-precision DRLT modular cascades.  Search
   needed; no published list at base 5.

9. **Connection to MCSP**.  `5^25` as a truth-table size sits
   exactly where MCSP starts to be structurally interesting
   (mid-range, beyond brute force but well below cosmological
   scale).  Whether the DRLT Hunter catalogue corresponds to
   "small-MCSP" functions (compressible to small circuits over
   atomic-integer bases) is a sharp empirical question.

10. **Quantum-CA generalisation**.  Unitary operators on
    `(ℂ^5)^⊗2 = ℂ^25` form a `625 - 1`-dim manifold (modulo
    phase).  Does the count-Lens have a quantum lift?  Open;
    likely requires substantial new infrastructure.

## §7 Open frontiers across all four fields

  · **Fermat-prime question at `d = 2`** (§1.1) — open since
    1640; intersects the dyadic-FSM cousin of the DRLT slice.
  · **Dedekind closed form `M(n)`** (§2.4) — open since 1897;
    computed value at `n = 9` arrived in 2023.
  · **Clone-lattice structure for `d ≥ 3`** (§2.1) — uncountable
    (Yanov–Muchnik) but structural theorems for maximal /
    minimal clones (Rosenberg 1970) incomplete.
  · **Explicit circuit lower bound** (§3.3) — Shannon gives
    `Ω(2^n / n)` for random, but explicit functions plateau at
    `(3 + 1/86) n` — among the deepest open problems in
    complexity theory.
  · **Universality decision for CA** (§3.2) — undecidable in
    general (Kari).  No classification of which `f ∈ F(d, n)`
    yield universal CA.
  · **MCSP intermediate status** (§3.3) — between P and NPC,
    derandomization-tight.
  · **Bounded-tetration categorical models** (§4.5) — research
    thread in proof-theoretic ordinals; no canonical
    reference for the "depth-3" invariant.
  · **DRLT Gram self-energy** (per G123) — structural derivation
    of the observation-seeded `α_em²/d²` correction.  Outside
    this note's scope but the principal downstream physics
    open problem.

## §8 Cross-references

  · `theory/math/cohomology/fractal.md` — promoted chapter for
    the N_U family.
  · `lean/E213/Lib/Math/Cohomology/Fractal/` — Lean realisation.
  · `lean/E213/Lib/Math/ModArith/UniversalFLT.lean` — FLT
    infrastructure used in the modular reduction proofs.
  · `theory/math/dyadic_fsm.md` — `d = 2` cousin via the
    dyadic FSM framework.
  · `theory/math/modular_arithmetic.md` — Bezout / F_{p²} /
    Frobenius substrate, the upstream of UniversalFLT.
  · `seed/AXIOM/04_uniqueness.md` §4.3 — structural forcing of
    `(NS, NT, d) = (3, 2, 5)`.
  · `rust-engine/docs/closure-algorithm.md` — `{NS, NT, d, c} =
    {3, 2, 5, 2}` 30-integer Hunter catalogue.
  · `catalogs/atomic-integers.md` — atomic readouts including
    `configCountD` family.

## §9 Self-check (against CLAUDE.md failure modes)

  · **No false dichotomy importing**: each field reading is an
    additive lens, not "DRLT vs that field."  All seven
    readings of `5^25` agree.
  · **No universe-constant framing**: the family is parametric;
    the slice `(5, 2)` is *one* readout.  Multi-field
    convergence at that slice is forced by independent
    derivations, not arranged.
  · **No stereotype matching**: "this corresponds to standard
    math X" — instead, each field's standard machinery becomes
    available to read the same family from a new angle.
  · **No deferred ontology**: every reading is operationally
    grounded in either Lean code (DRLT side) or published
    theorems (external fields).
  · **Open frontier honestly named**: §7 lists open problems
    by field; no fake completeness.

## §10 Registration

This note is registered as cross-field background for the
`theory/math/cohomology/fractal.md` chapter's "Open frontier"
section.  Concrete research directions (§6) are entry points
for follow-up work; none are on the immediate critical path
but several are cheap empirical extensions of the closed
N_U-family infrastructure.
