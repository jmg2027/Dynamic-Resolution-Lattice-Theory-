# Fractal-lens Cardinality — the N_U family

**Status**: Closed in `lean/E213/Lib/Math/Cohomology/Fractal/`
(5 files, 79 theorems, all strict ∅-axiom PURE).

## Overview

The **N_U family** is the parametric count-Lens output of the
resolution lattice — a 2-parameter family

```
configCountD : Nat → Nat → Nat
configCountD d n := d ^ (d ^ n)
```

reading: the number of distinguishable configurations of a
level-`n` fractal complex with `d^n` vertices, each carrying `d`
distinguishable states.

Three equivalent readings (∅-axiom):
1. **Combinatorial**: the count of `n`-variable `d`-valued
   functions `[d]^n → [d]`.
2. **Lens**: count-Lens readout at fractal depth `n` over base `d`.
3. **Cohomological**: the `d`-colouring count of the complete
   graph `K_{d^n}`.

The physics lens selects the slice `(d, n) = (5, 2)`:
  · `d = 5` is **forced** by `Theory.Atomicity.Five.atomic_iff_five`
    — under arity = 2 and atomicity, the unique `n` with a unique
    alive Diophantine decomposition `n = 2a + 3b` is `n = 5`.
    Corroborated by C2a (cohomology-loss `c·m·n = m²+m+n−2`) and
    C2b (adjoint-product `(m²−1)(n²−1) = (m+n)²−1`) constraints
    in `Lib/Physics/Foundations/AtomicConstantsUnique.lean` —
    three independent ∅-axiom proofs converge on
    `(NS, NT, c, d) = (3, 2, 2, 5)`.
  · The level `n = 2` is the canonical readout for the
    `K_{3,2}^{(c=2)} → K_{25}` fractal closure (rank-2 = pair
    structure).
  · The numerical value
    `configCountD 5 2 = 5^25 = 298 023 223 876 953 125`
    is the slice display-aliased `N_U` in
    `Lib/Math/ResolutionLimit.lean`.

The single canonical citation point is the umbrella
`Lib/Math/Cohomology/Fractal.lean`, which re-exports the five
sub-modules.  No `def N_U` exists anywhere in the source; the
display alias `abbrev N_U := configCountD 5 2` is the only
binding of the name.

## Lean source

- **Umbrella**: `lean/E213/Lib/Math/Cohomology/Fractal.lean`
- **Tree INDEX**: see umbrella docstring
- **File count**: 5 .lean files
- **∅-axiom status**: 79 PURE / 0 DIRTY

### Files

| File | Lines | PURE | Responsibility |
|---|---:|---:|---|
| `Level.lean` | 77 | 11 | Base-`5` fractal vertex count `numV (L) := 5^L`; edge / Betti spectrum of `K_{5^L}` at L = 1..4 |
| `ConfigCount.lean` | 226 | 20 | Parametric `configCountD d n := d^(d^n)`; structural identities + monotonicity + diagonal hit + per-d table |
| `ConfigCountModular.lean` | 376 | 35 | Modular fingerprint of the family: per-prime parametric reductions + period-2 capstones + the unified `configCountD_5_modular_structure` |
| `V25.lean` | 91 | 8 | `5²⁵` level-2 enumeration witness — vertex/edge/Betti of `K_{25}` |
| `AlphaGUT.lean` | (existing) | 5 | `α_GUT = 6/(25π²)` as the level-2 cardinality ratio |

### Key supporting external dependencies

  · `Lib/Math/ModArith/UniversalFLT.universal_flt_main` —
    Fermat's Little Theorem, supplies the `a^(p-1) % p = 1 % p`
    hypothesis to the parametric modular reduction.
  · `Meta/Nat/MulMod213.mul_mod_pure`,
    `Meta/Nat/AddMod213.{div_add_mod, mod_mod}` —
    213-native modular arithmetic helpers.
  · `Meta/Tactic/NatHelper.mul_assoc` — used inside the
    `pow_add_pure` and `pow_mul_pure` helpers, which the
    modular layer reuses.

## The narrative

### 1. The family — not a constant

Two parameters index the count-Lens output of the resolution
lattice:

  · The **level** `n` controls fractal depth.  At level `n` the
    complex has `numV(n) = d^n` vertices.  The count-Lens reads
    `configCountD d n = d^(d^n)` configurations.  The level is
    a free `Nat`, with no upper bound at the mathematics layer.
  · The **base** `d` controls per-vertex state cardinality.
    The arithmetic family is well-defined for any `d : Nat`;
    sample values at `n = 2` include `configCountD 2 2 = 16`,
    `configCountD 3 2 = 19683`, `configCountD 5 2 = 5^25`,
    `configCountD 7 2 = 7^49`.

Calling any *single* value of the family "the resolution
constant" silently picks both parameters and bakes the choice
into a name.  The chapter resolves this by giving the family a
first-class identifier (`configCountD`) and by citing the
structural forcing chain for the physics-relevant slice
`(d, n) = (5, 2)`.  The CLAUDE.md "Universe-constant framing"
failure-mode catalogue marks the conflation explicitly.

### 2. The structural forcing of `d = 5`

Three independent axiom-clean Lean derivations converge on
`(NS, NT, d) = (3, 2, 5)`:

1. **PairForcing chain** (`Theory/Atomicity/`).
   `NonDecomposable.lean:48-73` proves that the only non-
   decomposable integers `≥ 2` are `2` and `3` (anything else
   splits as `2 + (n−2)`).  `PairForcing.lean:141-194` proves
   that `count(p, q) = ⌊p/2⌋ · ⌊q/2⌋ = 1` iff `(p, q) = (2, 3)`
   for coprime `2 ≤ p < q`.  `Five.lean:134-135` concludes
   `atomic_iff_five : Atomic n ↔ n = 5` — under arity = 2 and
   the alive-parity predicate, the unique `n` with a unique
   alive Diophantine `n = 2a + 3b` is `n = 5`, witnessed by
   `(a, b) = (1, 1)`.

2. **C2b — adjoint-product identity**
   (`Lib/Physics/Foundations/AtomicConstantsUnique.lean:55-258`).
   The Lie-algebraic relation `(m² − 1)(n² − 1) = (m + n)² − 1`
   admits unique solution `(m, n) = (3, 2)` with `m, n ≥ 2`,
   verified by exhaustive search up to 300 plus closed-form
   Diophantine analysis for `n ≥ 4`.  This constrains the
   dimensions of the adjoint representations of
   `SU(m) × SU(n)`, with no α_em or other physics constant
   entering the derivation.

3. **C2a — cohomology-loss equation** (ibid., line 52).
   `c · m · n = m² + m + n − 2` couples the third atomic
   integer `c = 2` to `(m, n) = (3, 2)`.  Triple intersection at
   `(m, n, c, d) = (3, 2, 2, 5)`.

The three chains share no premises beyond Clause 4 of the
axiom (no self-pair `x/x`).  Their agreement is the strongest
internal evidence that `d = 5` is *forced*, not chosen.

### 3. Clean recursion — the canonical level-up

The single most useful identity of the family is

```
configCountD_succ : configCountD d (n + 1) = (configCountD d n) ^ d
```

(`ConfigCount.lean`).  Reading: levelling up by one **raises
the count to the `d`-th power**.  Proof goes through the
213-native `pow_mul_pure : a^(m * k) = (a^m)^k` together with
the definitional unfolding `d^(d^(n+1)) = d^(d^n * d)`.

The recursion gives, at one bound, every structural fact
downstream:
  · base values `configCountD d 0 = d`, `configCountD d 1 = d^d`
  · positivity: `1 ≤ d → 1 ≤ configCountD d n`
  · monotonicity in `n`: `configCountD d n ≤ (configCountD d n)^d`
    for `d ≥ 1` (so `configCountD d (n+1) ≥ configCountD d n`)
  · monotonicity in `d` (via a 3-step chain through `d^(e^n)`)
  · the diagonal hit: `configCountD d d = d^(d^d) = d ↑↑ 3`

The `Nat.pow_mul` / `Nat.pow_succ` lemmas from Lean core bring
`propext` through `rw`-style rewrites.  The chapter rebuilds
the needed identities as 213-native `pow_add_pure` /
`pow_mul_pure` via structural recursion on the exponent +
`Eq.subst` (`▸`) + `mul_assoc` from `Meta/Tactic/NatHelper` —
all ∅-axiom PURE.

### 4. Modular fingerprint at the physics base

The parametric Fermat-style reduction

```
pow_mod_period_pure (a p : Nat) (h_flt : a^(p-1) % p = 1 % p) (k : Nat) :
    a^k % p = a^(k % (p-1)) % p
```

(`ConfigCountModular.lean`) feeds the FLT hypothesis into a
clean exponent reduction, proved by composing `pow_add_pure`,
`pow_mul_pure`, `mul_mod_pure`, `div_add_mod`, and the helper
`pow_mod_one_pow_pure : b % p = 1 % p → ∀ q, b^q % p = 1 % p`.

The corollary on the family is

```
configCountD_mod_pure (d p : Nat) (h_flt : d^(p-1) % p = 1 % p) (n : Nat) :
    configCountD d n % p = d^((d^n) % (p-1)) % p
```

Instantiating at four primes (`p ∈ {3, 7, 11, 13}`) via
`UniversalFLT.universal_flt_main` plus `prime_gcd_*` witnesses
yields the following per-prime characterisation at the physics
base `d = 5`:

| `p` | period structure of `configCountD 5 n % p` |
|---:|---|
| 2 | constant `1` for all `n` (family is odd) |
| 3 | constant `2` for all `n` (`5^n` is odd ⇒ `5^(5^n) ≡ 2 mod 3`) |
| 5 | constant `0` for all `n` (positive power of 5) |
| 7 | period 2 from `n = 0` (alternates `5, 3, 5, 3, …`) |
| 11 | ★ eventually constant `1` from `n = 1` (`configCountD_5_succ_mod_11`) |
| 13 | period 2 from `n = 0` (`5^2 ≡ 1 mod 12`) |

The unified `configCountD_5_modular_structure` bundles the
mod-{2, 3, 5, 7, 13} fingerprint into a single statement.
`configCountD_5_mod_7_table` gives the closed-form even/odd
lookup: `configCountD 5 (2k) % 7 = 5`,
`configCountD 5 (2k+1) % 7 = 3`.

#### Extended modular fingerprint — `ConfigCountModular.lean §H`

Beyond the small prime layer `{2, 3, 5, 7, 11, 13}`, the
fingerprint extends to `{17, 23, 31, 41, 137}`.  The pattern is
*not* uniform period-2; new cycle structures emerge:

| `p` | cycle length | parametric closure |
|---|---|---|
| 17 | 4 | `configCountD_5_period_4_mod_17` (★ ∀m) |
| 23 | 5 | table (parametric deferred — 5-step template) |
| 31 | 2 | `configCountD_5_period_2_mod_31` (★ ∀m) |
| 41 | 1 (constant) | `configCountD_5_succ_mod_41` (★★ ∀m) |
| 137 | 16 | table; parametric deferred (16-step template) |

The proofs at `p ∈ {17, 31, 41}` use a shared template:
induct on `m`, propagate via `pow_mul_pure` + the auxiliary
`pow_mod_base` lemma, close each substep with a decidable
cycle fact `(cycle_i)^5 % p = cycle_{i+1}`.  Cycle-length 1
(fixed point at `p = 41`) is the structurally simplest; lengths
2, 4 follow the same template with proportional code growth.

##### The α series

The two α-catalogue primes produce structurally distinguished
readouts:

```
α_GUT integer (p = 41):
  ★ configCountD 5 n ≡ 9 = NS² (mod 41)   for all n ≥ 1.
  Fractal-level-invariant: the α_GUT residue is fixed under
  level iteration.  Cleanest result in the extended catalogue.

α_em integer (p = 137 = 1/α_em):
  configCountD 5 2 ≡ 86 = Rn (mod 137).
  86 = NS²·NT² + d²·NT   (Hunter form, additive).
  Cycle length 16 in n; the physics-slice readout (`n = 2`) lands
  on the catalogue atom `Rn` (radon atomic number).
```

Both readouts (`9, 86`) are themselves catalogue atoms.  The
count-Lens at each α prime projects `N_U` to a catalogue atom,
but only `α_GUT` does so uniformly across all `n`.  The
`(p, value) = (α_GUT, NS²)` pair is the cleanest cross-readout
between physics-constants atoms and count-Lens outputs.

The `α_em` readout is a single-slice resonance: `N_U mod 1/α_em
= Rn` connects two catalogue atoms but doesn't extend to a
fractal-level invariant.  The 16-step cycle is the next-level
algebraic complication.

##### Cycle-template scaling

The three closed parametric proofs at `p ∈ {41, 31, 17}` span
cycle lengths 1, 2, 4, demonstrating that the
`pow_mul_pure + pow_mod_base + k cycle seeds + k substeps`
template scales to arbitrary cycle length.  Each new cycle
length adds O(k) lines of Lean (k seeds + k substep blocks);
no new structural lemmas required.

For `p = 17` the m=0 base case requires
`set_option exponentiation.threshold 1000` to handle
`5^(5^4) = 5^625` without triggering Lean's default reduction
limit.  Larger cycle lengths need correspondingly higher
thresholds; this is a compile-time directive, not an axiom
addition.

### 5. Combinatorial reading + diagonal-tetration coincidence

`configCountD d n` equals the count of functions `[d]^n → [d]`,
i.e. `n`-variable `d`-valued truth tables.  At `(d, n) = (2, n)`
this is the count of `n`-variable Boolean functions; at
`(d, n) = (5, 2)` it is the count of `2`-variable `5`-valued
functions — the latter coinciding with the value display-
aliased `N_U`.

The diagonal `n = d` gives a clean tetration hit:

```
configCountD d d = d ^ (d ^ d) = d ↑↑ 3
```

(`configCountD_diagonal`).  For `d = 2` this is `2 ↑↑ 3 = 16`
(and equals `configCountD 2 2`); for `d = 5`, `5 ↑↑ 3 = 5^3125`,
far larger than the level-2 value `5^25`.  The DRLT slice
`(5, 2)` is **off-diagonal** but structurally forced; the
diagonal is mathematically natural but physically unrealised.

### 6. Fractal Betti spectrum (the level-counting side)

`Level.lean` records the fractal-vertex / edge / Betti
spectrum of `K_{5^L}` at small `L`:

| `L` | `numV = 5^L` | `numE = C(5^L, 2)` | `b₁ = (5^L − 1)(5^L − 2)/2` |
|---:|---:|---:|---:|
| 1 | 5 | 10 | 6 |
| 2 | 25 | 300 | 276 |
| 3 | 125 | 7 750 | 7 626 |
| 4 | 625 | 195 000 | 194 376 |

The Euler identity `b₁(L) = numE(L) − numV(L) + 1` is
decide-checked at each `L`.  The spectrum gives the
*topological* counterpart to the *count-Lens* readout
`configCountD 5 L`: same fractal, different Lens output.

### 7. Parametric, no privileged level

`configCountD d n` is bare combinatorics, parametric in both base
and level.  No level is privileged: `n ↦ configCountD d n` is a
strict order-embedding (`configCountD_strictMono` for `d ≥ 2`),
so no count can be crowned as "the resolution / universe number".
`configCount 2 = 5²⁵` is a true arithmetic value, nothing more.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `configCountD` | `Fractal.ConfigCount` | `d^(d^n)` definition |
| `configCount` | `Fractal.ConfigCount` | display alias `configCountD 5 n` |
| `configCount_two` | `Fractal.ConfigCount` | `configCount 2 = 298_023_223_876_953_125` |
| `configCountD_succ` | `Fractal.ConfigCount` | `configCountD d (n+1) = (configCountD d n)^d` |
| `configCountD_diagonal` | `Fractal.ConfigCount` | `configCountD d d = d^(d^d)` (= `d↑↑3`) |
| `configCountD_pos` | `Fractal.ConfigCount` | `1 ≤ d → 1 ≤ configCountD d n` |
| `configCountD_mono_n` | `Fractal.ConfigCount` | levelling up never decreases the count |
| `configCountD_mono_d` | `Fractal.ConfigCount` | base monotonicity (with `1 ≤ d`) |
| `pow_add_pure` / `pow_mul_pure` | `Fractal.ConfigCount` | 213-native power identities |
| `pow_mod_period_pure` | `Fractal.ConfigCountModular` | parametric Fermat-style reduction |
| `configCountD_mod_pure` | `Fractal.ConfigCountModular` | family-level corollary |
| `configCountD_5_modular_structure` | `Fractal.ConfigCountModular` | ★★★ unified mod-{2, 3, 5, 7, 13} capstone |
| `configCountD_5_mod_7_table` | `Fractal.ConfigCountModular` | even/odd closed-form lookup |
| `configCountD_5_succ_mod_41` | `Fractal.ConfigCountModular` §H.1 | ★ constant `9 = NS²` mod `41 = α_GUT` for all `n ≥ 1` |
| `configCountD_5_period_2_mod_31` | `Fractal.ConfigCountModular` §H.3 | ★ period-2 `{25, 5}` mod 31 ∀m |
| `configCountD_5_period_4_mod_17` | `Fractal.ConfigCountModular` §H.4 | ★ period-4 cycle `(14, 12, 3, 5)` mod 17 ∀m |
| `configCountD_5_succ_mod_11` | `Fractal.ConfigCountModular` §I | ★ eventually constant `1` mod `11` ∀n ≥ 1 (fixed-point absorption of `5^n mod 10`) |
| `configCountD_5_2_mod_137` | `Fractal.ConfigCountModular` §H.5 | ★ `N_U mod 1/α_em = 86 = Rn` (catalogue cross-readout) |
| `configCountD_5_2_mod_table_extended` | `Fractal.ConfigCountModular` §H | physics-slice readouts mod `{17, 23, 31, 41}` |
| `fractal_betti_spectrum` | `Fractal.Level` | `b₁(K_{5^L})` for `L = 1..4` |
| `numV_eq_d_sq` | `Fractal.V25` | `numV = d² = 25` (level-2 enumeration) |
| `configCountD_strictMono` | `Fractal.ConfigCount` | `n ↦ configCountD d n` strictly increasing (`d ≥ 2`): no privileged level |

## Research-note provenance

Foundational notes that fed this chapter live in
`research-notes/archive/`:

  · N_U re-derivation plan — diagnosis of three syntactically
    distinct `def N_U` definitions and the four-Lens
    convergence fiction; resolution by demoting `N_U` to an
    abbrev over the parametric family.
  · N_U family theory note — 7-phase plan for the
    d-generalisation, modular reduction via FLT, and physics
    bridges; multi-agent debate transcript across four
    parallel research agents (number theory, structural
    origin, Lean roadmap, physics consequences).

The algebraic backdrop — Möbius `P = [[2,1],[1,1]]` with
`disc = NS + NT = 5` and Pell-Fibonacci signature — appears in
`seed/AXIOM/03_form.md` §3.5 and `seed/AXIOM/04_uniqueness.md`
§4.3.

## Open frontier

  · **Base-5 Wieferich primes** (empirical, Lean-deferred).  A
    prime `p` is Wieferich-base-5 iff `5^(p−1) ≡ 1 (mod p²)`.
    Brute-force search at `p ∈ [7, 10⁵]` identifies exactly two:
    `p = 20771` and `p = 40487` (matches OEIS A123693).  These
    obstruct higher-precision base-5 modular cascade — at
    non-Wieferich primes the lift `p → p²` adds no algebraic
    complication; at Wieferich primes the FLT period `p − 1`
    no longer suffices and a finer period analysis modulo `p²`
    is required.  Lean closure is kernel-impractical (~14500-digit
    intermediate values); recorded as falsifier-catalogue
    candidate.  Pattern via `(p − 1)`: both share the factor
    `31` (where `configCountD 5 n` exhibits the period-2 mod-31
    readout) — structural or coincidental is open.

  · **Affine-plane reading at `(d, n) = (5, 2)`** — algebraic-
    geometric handle on `N_U`.  Identifying `[5]` with `F_5`,
    `5^25 = |F_5[x, y] / (x^5 − x, y^5 − y)|` is the cardinality
    of the polynomial function ring on the affine plane `A²_{F_5}`.
    The internal question: does the `K_{3,2}^{(c=2)} → K_{25}`
    closure functor correspond to a specific sub-ideal of this
    function ring?  Candidate sub-spaces (degree-bounded `R_{≤k}`,
    symmetric `R^{sym}`, multilinear `R^{lin}`, bipartite-supported)
    are enumerable with cardinalities `5^k` for various `k ≤ 25`.
    Closure requires `F_q` polynomial-ring infrastructure not yet
    present in `lean/E213/` — substantive multi-session addition
    on the scale of the Real213-p-adic infrastructure.

  · **Cross-field cross-imports at `(d, n) = (5, 2)`** — the
    integer `5^25` admits **seven independent readings**
    (combinatorial / cohomological / Cartesian-closed / type-
    theoretic / cellular-automata / algebraic-geometric / lattice-
    internal).  All seven agree on the value, providing
    independent witnesses that the physics slice is structural
    rather than chosen.  Concrete cross-import directions:
    Aurifeuillean factor reading of `N_U + 1` cofactors
    (overlap with `aurifeuillean.md`); finite-field affine-plane
    sub-ideal correspondence (above); Łukasiewicz `L_5`
    functional-completeness reformulation of the Lens framework
    (since 5 is prime, Rosser–Turquette applies); iterated
    Carmichael chain beyond `{2, 3, 5, 7, 11, 13}`; tetration-
    depth-3 categorical invariant `F(5, 5) = 5^3125`; Sheffer-
    fraction of `F(5, 2)`; reversible-CA fraction `25! / 5^25`;
    MCSP-mid-range connection; quantum-CA unitary lift on `ℂ^25`.
    None of these is on the immediate critical path; each is a
    cheap empirical extension of the closed N_U-family
    infrastructure.

  · **Structural derivation of the Gram self-energy term**
    (`Lib/Physics/AlphaEM/Augmented.lean:134-141`).  The
    `213/10⁸` correction that brings `1/α_em` below the ppb
    bracket is evaluated at the *observed* `α_em`, not derived
    from atomic primitives.  Closing this gap removes the only
    observation-seeded coefficient in the precision-Lens
    validation standard.  Out of scope for the cohomology
    layer; logged here as the principal downstream physics
    problem.
  · **Pisano-analogue grid across sister sequences** — extends
    to the small-prime pentad `{2, 3, 5, 7, 11}` for 4 of 6
    sister sequences:

    | Sequence  | π(2)       | π(3) | π(5) | π(7) | π(11) |
    |-----------|------------|------|------|------|-------|
    | Fibonacci |   3        |   8  |  20  |  16  |  10   |
    | Lucas     |   3        |   8  |   4  |  16  |  10   |
    | Padovan   |   7        |  13  |  24  |  48  | (120) |
    | Tribonacci|   4        |  13  |  31  |  48  | (110) |
    | Narayana  |   7        |   8  |  31  |  57  |  60   |
    | Jacobsthal| constant 1 |   6  |   4  |   6  |  10   |

    27 parametric + 1 eventually-constant closures shipped;
    Padovan / Tribonacci mod 11 (periods 120 / 110) deferred.

    Common technique: nested induction over the recurrence
    order + `add_mod_gen` for sum reduction + `mul_mod_right_pure`
    for multiplicative coefficients (Jacobsthal `2 J_n`).
    Period-coincidence twins: Fib ↔ Lucas (shared recurrence
    matches all periods); Padovan ↔ Narayana share π(2) = 7;
    Lucas ↔ Jacobsthal share π(5) = 4 via different structural
    origins; Tribonacci ↔ Narayana share π(5) = 31.  Jacobsthal
    mod 2 uniquely collapses to constant (rather than nontrivial
    periodic) due to the `2 J_n` term.

  · **General eventual-periodicity statement** at arbitrary
    coprime `(d, p)` — **CLOSED**.
    `EventualPeriodicity.lean` ships the universal form
    `configCountD_eventually_periodic (d p' : Nat)
      (h_flt : d ^ (p' + 2 - 1) % (p' + 2) = 1 % (p' + 2)) :
      ∃ T n₀, 1 ≤ T ∧ n₀ ≤ p' + 2 - 1
        ∧ ∀ n, n₀ ≤ n
            → configCountD d (n + T) % (p' + 2)
              = configCountD d n % (p' + 2)`
    via forward-only pigeonhole on the exponent layer
    `n ↦ d^n % (p - 1)` (Markov chain on `Fin (p - 1)`) +
    `configCountD_mod_pure` bridge.  Distinct from
    `MulOrderPigeonhole.exists_modPow_period`: no modular inverse
    needed, so applies to the eventually-constant regime
    `gcd(d, p - 1) ≠ 1` (witnessed at `(5, 11)`) as well as the
    purely periodic regime.  Concrete period-2 capstones at
    `(5, 7)`, `(5, 13)` and eventually-constant capstones at
    `(5, 11)`, `(5, 41)` remain available as sharper closures.
    Padovan / Tribonacci / Fibonacci / Narayana Pisano-analogue
    parametric closures at the exponent-free recurrence level
    are shipped in `{Padovan, Tribonacci, Fibonacci,
    Narayana}Modular.lean`.
  · **Combinatorial-identity Lean witness**: the truth-table
    reading `configCountD d n = | [d]^n → [d] |` is currently
    a docstring identity.  A `Fintype.card`-style Lean theorem
    would make the reading first-class, but `Fintype`
    machinery is not yet 213-native in `lean/E213/`.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Cohomology.Fractal
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Fractal.ConfigCount
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Fractal.ConfigCountModular
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Fractal.Level
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Fractal.V25
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Fractal.AlphaGUT
```

Expected: build clean; each scan reports `N PURE / 0 DIRTY`
with totals `11 + 20 + 35 + 8 + 5 = 79 PURE / 0 DIRTY`.
