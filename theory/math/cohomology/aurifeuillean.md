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
  · `theory/math/modular_arithmetic.md`: Pell-Fibonacci
    substrate over `F_{p²}`, the modular reduction of the same
    `ℤ[√d]` extension.
  · `theory/math/dyadic_fsm.md`: the dyadic FSM closure traces
    the same `ℤ[√5]` algebraic structure under bit-stream
    reduction.
  · `lean/E213/Lib/Math/Mobius213.lean`: Möbius `P(x) = (2x+1)/(x+1)`
    fixed point lives in `ℤ[√5]`.

Together: the physics base `d = 5` (selected by the three-pillar
forcing in `Theory.Atomicity.Five`) algebraically demands an
`ℤ[√5]`-aware computation layer.  The Aurifeuillean handle
`(29, 8) = (d² + NT², NT³)` is one face of that demand; the
golden-ratio / Möbius / Pell-Fibonacci structures are other
faces of the same algebraic requirement.

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

Lib/Math/Cohomology/Fractal/ConfigCountAurifeuilleanParam.lean  (5 PURE)
  · pow_mod_base                          — private aux (induction)
  · five_pow_5_mod_521, five20_pow_5_mod_521  — private seeds
  · five_pow_five_pow_succ_mod_521        — parametric ≡ 520
  · aurifeuillean_universal               — ★ ∀m, (cC (m+1) + 1) % 521 = 0
  · aurifeuillean_at_n_eq_{1,2,3}         — specialisations
```

`#print axioms aurifeuillean_universal  →  "does not depend on any
axioms"`.  All 16 theorems strict ∅-axiom PURE.  Build clean.
