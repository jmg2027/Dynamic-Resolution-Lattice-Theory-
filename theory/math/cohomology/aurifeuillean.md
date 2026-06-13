# Aurifeuillean handle on `N_U + 1`

**Status**: Closed in `lean/E213/Lib/Math/Cohomology/Fractal/`
(`ConfigCountAurifeuillean.lean` + `ConfigCountAurifeuilleanParam.lean`,
16 PURE theorems, all strict ∅-axiom).

## Overview

The N_U family `configCountD d n := d^(d^n)` is closed in
`theory/math/cohomology/fractal.md`.  The companion family
`d^(d^n) + 1` carries an additional algebraic structure: the
**Aurifeuillean cyclotomic factorisation**, which produces a
single prime that divides every member of the sequence
uniformly across the fractal-level parameter `n`.

At the physics-selected base `d = 5`:

```
∀ n ≥ 1,  521 ∣ 5^(5^n) + 1.
```

The divisor `521` is the *unique* Aurifeuillean cyclotomic
factor of the family, and admits the algebraic-number-theoretic
representation

```
521 = Φ_10(5)
    = 29² − 5 · 8²
    = N(29 + 8√5)         in ℤ[√5]
```

where `N : ℤ[√d] → ℤ` is the field norm of `ℚ(√d)`.

## Cyclotomic decomposition of the sequence

For `k = 5^n` with `n ≥ 1`:

```
5^k + 1 = ∏_{d ∣ 2k, d ∤ k} Φ_d(5)
        = Φ_2(5) · Φ_10(5) · Φ_50(5) · … · Φ_{2·5^n}(5)
```

The Aurifeuillean condition (Schinzel–Brent): for squarefree
base `b ≡ 1 (mod 4)`, cyclotomic index `n` admits an
`ℤ[√b]`-factorisation iff `n = 2 · b · m²` with `m` odd
squarefree and `gcd(m, b) = 1`.

For `b = 5`:
  · `m = 1 → n = 10`: `Φ_10(5) = 521` *is* Aurifeuillean.
  · `m = 3 → n = 90`: `Φ_90(5) = 60081451169922001` *is*
    Aurifeuillean.
  · `m = 7 → n = 490`: `Φ_490(5)` *is* Aurifeuillean (~117 digits).
  · `n = 50 = 2 · 5²`: would require `m² = 5`, no integer solution.
    NOT Aurifeuillean.
  · `n = 250 = 2 · 5³`: ditto NOT Aurifeuillean.

The intersection of "appears in the decomposition of `5^(5^n) + 1`
for some `n ≥ 1`" and "Aurifeuillean" is the singleton `{Φ_10(5)}`.
`Φ_90(5), Φ_490(5)` are Aurifeuillean but do **not** appear in
the `5^(5^n) + 1` decomposition (the indices `90, 490` are not of
the form `2 · 5^n`).  `Φ_50(5), Φ_250(5)` appear in the
decomposition but are **not** Aurifeuillean.

So `Φ_10(5) = 521` is the **unique** n-uniform Aurifeuillean
handle on the family.

## Parametric divisibility

The structural proof of `∀ n ≥ 1, 521 ∣ 5^(5^n) + 1` uses no FLT,
no period reduction, no Carmichael — only the seed identity and
the algebraic structure of iterated exponentiation.

**Seed**: `5^5 + 1 = 6 · 521`, i.e. `5^5 ≡ −1 (mod 521)`.

**Induction**: `5^(5^(m+1)) = (5^5)^(5^m)` via the algebraic
identity `5^(5^(m+1)) = 5^(5 · 5^m) = (5^5)^(5^m)`.  Working
modulo `521`:

```
5^(5^(m+1)) ≡ (5^5)^(5^m) ≡ (−1)^(5^m) ≡ −1 (mod 521)
```

since `5^m` is odd for every `m`.

Lean realisation: `aurifeuillean_universal` in
`Lib/Math/Cohomology/Fractal/ConfigCountAurifeuilleanParam.lean`,
proved by induction on `m` with the auxiliary lemma `pow_mod_base`
(`a^k % p = (a % p)^k % p`) and two decidable seeds
(`5^5 % 521 = 520` and `520^5 % 521 = 520`).

## Hunter-primitive expressibility (m=1 slice)

The Aurifeuillean L-coefficient pair `(29, 8)` for `Φ_10(5)`
admits Hunter-primitive expressibility at the physics-selected
slice:

```
29 = d² + NT²    = 25 + 4
   = NT^d − NS   = 32 − 3
   = d² + d − 1  = 25 + 5 − 1
8  = NT³        = 2³                  (catalogue atom)
```

Three independent atomic readings of `29` all hold simultaneously.
The cleanest (subtraction-free) form is `29 = d² + NT²`, giving

```
521 = (d² + NT²)² − d · (NT³)²       in Hunter primitives.
```

Equivalently `521 = N((d² + NT²) + NT³ · √d)` in `ℤ[√d]`.

**Localisation**: this Hunter ⇔ Aurifeuillean correspondence
holds *only* at the minimal index `m = 1`.  The next
Aurifeuillean cyclotomic factor at base `d = 5` is

```
Φ_90(5) = 60081451169922001 = 850554441² − 5 · 364242064²
```

(a 17-digit prime), and neither `L = 850554441` nor
`M = 364242064` admits Hunter-primitive representation.
Reduction under unit multiplication in `ℤ[√5]` gives smaller
representatives, but the smallest `|M|` reached is
`(5^12 + 1)/2 = 122070313` — still a generic algebraic-integer
value, not a Hunter atom.

The Hunter-Aurifeuillean correspondence is therefore localised
to the **first non-trivial cyclotomic factor** at base `d = 5`
— the lowest discrete algebraic split before the cyclotomic
tower exits to higher-degree extensions.

## Structural significance

### Scale-free anchor

The hyper-exponential family `5^(5^n)` exits all realistic
computation regimes by `n = 3` (88-digit numbers) and `n = 4`
(~10³⁵ digits).  The Aurifeuillean handle `521` is preserved
exactly across every level:

  · `n = 1`: `5^5 + 1 = 6 · 521`
  · `n = 2`: `5^25 + 1 = 521 · 572021542950006` (the physics slice)
  · `n = 3`: `5^125 + 1` ≡ 0 (mod 521)
  · …

The residue class `Z/521Z` carries a complete `mod 521` shadow
of the entire `{5^(5^n) + 1 : n ≥ 1}` sequence, independent of
the sampling-regime explosion in the underlying integers.

### `ℤ[√5]` algebraically forced

`Φ_10(x) = x⁴ − x³ + x² − x + 1` is irreducible over `ℤ`.  The
Aurifeuillean factorisation `Φ_10(5) = (29 + 8√5)(29 − 8√5)`
sits one ring up, in `ℤ[√5]`.

This requirement parallels structures already established in
the codebase:
  · `catalogs/atomic-integers.md` (φ section): `φ = (1+√5)/2`
    is the dominant eigenvalue of `[[2,1],[1,1]]` with
    characteristic polynomial `λ² − 3λ + 1` (trace `3 = NS`,
    determinant `1`, discriminant `5 = NS + NT`).
  · `theory/math/numbertheory/modular_arithmetic.md`: Pell-Fibonacci
    substrate over `F_{p²}`, the modular reduction of the same
    `ℤ[√d]` extension.
  · `theory/math/numbertheory/dyadic_fsm.md`: the dyadic FSM closure traces
    the same `ℤ[√5]` algebraic structure under bit-stream
    reduction.
  · `lean/E213/Lib/Math/Algebra/Mobius213.lean`: Möbius `P(x) = (2x+1)/(x+1)`
    fixed point lives in `ℤ[√5]`.

Together: the physics base `d = 5` (selected by the three-pillar
forcing in `Theory.Atomicity.Five`) algebraically demands an
`ℤ[√5]`-aware computation layer.  The Aurifeuillean handle
`(29, 8) = (d² + NT², NT³)` is one face of that demand; the
golden-ratio / Möbius / Pell-Fibonacci structures are other
faces of the same algebraic requirement.

### The cut-off line: scale matching of two independent frameworks

*(This section's structural content is generalised in
`theory/meta/cardinality_cutoff_principle.md` — the **cardinality
cut-off principle** as a 213-native methodology.  The Aurifeuillean
case here is the exemplar from which the principle was extracted.)*

The Hunter ⇔ Aurifeuillean correspondence at `(29, 8) = (d² + NT², NT³)`
is not merely "a clean numerical hit" — it is the location where two
**independently-defined structural frameworks** match in scale.

| Framework | Object generated | Scale at `Φ_{2bm²}(b)` for `b = 5` |
|---|---|---|
| **Aurifeuillean** (algebraic Galois split, external) | `(L_m, M_m)` ∈ ℤ[√5] | magnitude `~ 5^(φ(2·5·m²)/2)`, polynomial in 5 with degree growing as `m²` |
| **Hunter primitives** (computational atomicity, DRLT-internal) | `{NS, NT, d, c}^{depth ≤ k}` ∪ `(+, *, ^)` | bounded by tower function of `k`; standard atoms ≲ few thousand |

Concrete numerical scales:

```
m = 1 (Φ_10):   degree  2 → L₁ ~ 5²    ≈ 25            (actual: 29 = d² + NT²)   ✓ Hunter
m = 3 (Φ_90):   degree 12 → L₃ ~ 5¹²   ≈ 2.4 × 10⁸     (actual: 8.5 × 10⁸)        ✗ Hunter
m = 7 (Φ_490):  degree 84 → L₇ ~ 5⁸⁴   ≈ 10⁵⁹                                      ✗ Hunter
m = 9 (Φ_810): degree 108 → L₉ ~ 5¹⁰⁸  ≈ 10⁷⁵                                      ✗ Hunter
```

**Scale-matching slice**: the Aurifeuillean L-coefficient and the
"reasonable Hunter expression" value range overlap only at `m = 1`.
For `m ≥ 3`, Aurifeuillean instantly exceeds the Hunter expression
range achievable at small depth.  This is the **cut-off line** —
the boundary where two unrelated structural frameworks meet in
exactly one slice of the cyclotomic tower above `d = 5`.

### Last discrete Galois split before tetration

`configCountD d n = d^(d^n)` is depth-2 tetration, sitting at
Grzegorczyk class `ℰ³` (bounded exponentiation).  As `n` grows,
the cyclotomic indices `2 · 5^n` themselves become tetrationally
large, and the corresponding `Φ_{2·5^n}(5)` values approach the
Statman non-elementary boundary of βη-equivalence decidability
for finite-base STLC.

The Aurifeuillean split at index `n = 10` (the minimal
Aurifeuillean cyclotomic index above base `d = 5`) is the
*lowest-index* cyclotomic factor in the family that admits a
non-trivial `ℤ[√d]` factorisation with Hunter-primitive
L-coefficients.  Higher indices (`Φ_90, Φ_490, …`) lose the
Hunter signature and live in the generic `ℤ[√5]` prime-ideal
landscape.

The pair `(29, 8) = (d² + NT², NT³)` is therefore the cleanest
discrete algebraic signature visible at the bottom of the
hyper-exponential tower — a Galois-theoretic 'first
distinguishing' of the family before tetrational complexity
takes over.  Its expressibility in Hunter primitives is what
makes it a DRLT structural object rather than an arithmetic
coincidence.

### Bounded Lean realisation

The full cut-off claim ("Aurifeuillean L-coefficients beyond `m = 1`
admit no Hunter expression at any depth") is a conjecture about an
infinite family.  A **bounded version** is decidable and Lean-verified
in `Lib/Math/Cohomology/Fractal/AurifeuilleanCutoff.lean`:

  · **Positive (depth-3 witness)**:
    `hunter_521_explicit : NT^(NS^2) + NS^2 = 521`
    (`= 2^9 + 9 = 512 + 9 = 521`).  Three operations on `{NS, NT}`
    suffice to express `521` exactly.

  · **Negative (bounded parameter search)**:
    `L_90_not_pow_sum_pow : ∀ (a b c e : Fin 10),
                             a.val^b.val + c.val^e.val ≠ 850554441`.

    The Aurifeuillean L-coefficient at `Φ_90(5)` is **not expressible
    as `a^b + c^d`** for any `a, b, c, d ∈ {0, 1, …, 9}`.  Decidable
    via exhaustive enumeration (10⁴ cases).  Companion theorems
    cover the forms `a^b * c^d`, `(a + b)^c` over the same
    parameter range, and the M-coefficient `364242064`.

The honest interpretation of these bounded results:
  · They **confirm** the scale-mismatch numerically at the next
    Aurifeuillean index — `L = 850554441` is not reachable by
    "natural" depth-3 Hunter expressions with single-digit
    parameters.
  · They **do not** rule out exotic large-parameter Hunter
    expressions hitting the value (which would be needed for the
    full cut-off theorem).
  · They establish the conjecture at the bounded-decidable level —
    upgrading to a full theorem requires a complexity-theoretic
    lower bound on minimum Hunter expression depth for specific
    Aurifeuillean L values, or an enumerative argument over all
    bounded-depth Hunter expressions (currently intractable beyond
    depth 3-4).

## Catalogue cross-reference

`catalogs/atomic-integers.md` registers `521` under
"Large integers (100+)" with the norm representation, the three
atomic readings of `29`, and Lean cross-references.  `521` is
added to the "Atomic primes" list (joining `2, 3, 5, 7, 13, 41,
137`).

## Lean structure

```
Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean       (11 PURE)
  · aurifeuillean_norm_521                — 521 = 29² − 5·8²
  · aurifeuillean_norm_521_hunter         — Hunter-primitive form
  · phi_10_at_5                           — Φ_10(5) = 521 Nat-recast
  · five_pow_5_plus_one                   — seed 5^5 + 1 = 6·521
  · configCount_one/two/three_plus_one_mod_521  — concrete instances
  · configCount_one/two_plus_one_eq_mul_521     — exact cofactors
  · aurifeuillean_phi_90_at_5             — Φ_90(5) factor identity
  · aurifeuillean_fingerprint_n_u         — capstone at n=2

Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean        (28 PURE)
  · HunterTerm inductive type + eval, depth functions
  · t521 explicit depth-3 witness for 521 = NT^(NS^2) + NS^2
  · t29 (depth 2), t8 (depth 1) companion witnesses
  · frobenius_850554441 + literal_cutoff_vacuous_at_L_90
    — demonstrates the literal "∀ depth" cut-off is false (Chicken
      McNugget: 850554441 = 2·425277219 + 3 has a Hunter expression
      at huge depth)
  · L_90_not_at_depth_0, L_90_not_at_depth_1, M_90_not_at_depth_1
    — Fin-quantified bounded cut-off at depth ≤ 1
  · depth_1_value_bound — every depth-1 Hunter value ≤ 3125
  · asymptotic_cutoff_at_depth_1 — ★ ∀ v > 3125, v ∉ depth-1 Hunter
  · cutoff_marathon_at_depth_1 — ★★ capstone:
      (m=1 positive at depth 3) ∧ (∀ v > 3125 negative at depth 1)
    Captures the entire Aurifeuillean L tail (L_m for m ≥ 3, all
    ≫ 3125) at depth 1.

Lib/Math/Cohomology/Fractal/AurifeuilleanCutoff.lean            (9 PURE)
  · hunter_521_explicit          — 521 = NT^(NS²) + NS² (depth-3 witness)
  · hunter_29_explicit           — 29 = d² + NT²
  · hunter_8_explicit            — 8 = NT^NS
  · L_90_not_pow_sum_pow         — 850M ≠ a^b + c^d for a,b,c,d ∈ Fin 10
  · L_90_not_pow_mul_pow         — 850M ≠ a^b · c^d
  · L_90_not_sum_pow             — 850M ≠ (a+b)^c
  · M_90_not_pow_sum_pow         — 364M ≠ a^b + c^d
  · M_90_not_pow_mul_pow         — 364M ≠ a^b · c^d
  · bounded_cutoff_at_m3         — ★ capstone: m=1 ✓ Hunter, m=3 ✗ Hunter (bounded)

Lib/Math/Cohomology/Fractal/ConfigCountAurifeuilleanParam.lean  (5 PURE)
  · pow_mod_base                          — private aux (induction)
  · five_pow_5_mod_521, five20_pow_5_mod_521  — private seeds
  · five_pow_five_pow_succ_mod_521        — parametric ≡ 520
  · aurifeuillean_universal               — ★ ∀m, (cC (m+1) + 1) % 521 = 0
  · aurifeuillean_at_n_eq_{1,2,3}         — specialisations
```

`#print axioms aurifeuillean_universal  →  "does not depend on any
axioms"`.  All 16 theorems strict ∅-axiom PURE.  Build clean.
