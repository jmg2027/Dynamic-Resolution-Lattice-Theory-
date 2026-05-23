# Real213-p-adic — 213-native p-adic Numbers

**Status**: Closed (8 files, 308 PURE).

## Overview

**Real213-p-adic** is a 213-native, ∅-axiom construction of the
p-adic integers `ℤ_p` and p-adic numbers `ℚ_p`.  The library is
built on three layers:

1. **Foundation** — `ZpSeq p` as an infinite digit sequence
   `ℕ → Fin p`, with truncation `trunc : ℕ → ℕ` faithfully
   embedding into `ℤ/p^n`.
2. **Arithmetic** — `add`, `mul`, `neg` defined digit-by-digit
   via carry FSMs; the central ring-quotient theorems
   `add_trunc` and `mul_trunc` state that truncation is a ring
   homomorphism `ZpSeq → ℤ/p^n`.
3. **Inversion** — Hensel-lifted multiplicative inverse `invSeq`
   for units; correctness `mul_invSeq_correct` proves
   `x · invSeq n ≡ 1 (mod p^(n+1))` for all `n`.

Above this sit the propositional p-adic valuation (`Norm`), the
ℚ_p localization (`Field`), and the DRLT integration (5-adic lift
of `N_U = 5^25`).

The library is ∅-axiom throughout: every theorem reports
`#print axioms … → "does not depend on any axioms"`.  Mathlib's
`Padic` builds on Cauchy completion which brings `propext`,
`Quot.sound`, `Classical.choice`; Real213-p-adic brings none.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Padic/` (8 files)
- **Umbrella**: `Padic.lean`
- **∅-axiom status**: 308 PURE / 0 DIRTY

### Sub-cluster organization

| File | Topic |
|---|---|
| `Foundation.lean` | `ZpDigit`, `ZpSeq`, `trunc`, `zero`, `one`, `neg_one`, `eq_mod_pn`, `trunc_lt_p_pow`, `eq_mod_pn_iff_trunc`, `digits_of_nat` (embedding ℕ ↪ ZpSeq), `trunc_neg_one_succ`, `trunc_one_succ` |
| `Arith.lean` | `Zp.add` + carry FSM, `Zp.add_trunc`, `Zp.complement`, `Zp.neg`, `Zp.mul` + off-diagonal decomposition, `Zp.mul_trunc` (general bridge), `Zp.shiftLeft`, ring axioms at trunc (comm/assoc/distrib/add-inverse via `add_neg_self_trunc`), sub_eq_zero biconditional |
| `Pow.lean` | `Zp.pow x n` recursive, `pow_trunc` (homomorphism), `pow_add_trunc` / `pow_mul_trunc`, `pow_p_trunc_one` / `pow_p_minus_one_trunc_one` (Fermat at digit 0 / for units, p prime), `teichmuller_iter` (`x ↦ x^p` iteration), `valAtLeast_pow` |
| `Norm.lean` | `valAtLeast` / `valEq`, full ultrametric: `valAtLeast_add`, `valAtLeast_mul`, `valAtLeast_neg`, `valEq_add_of_lt` (strong: differing valuations), `valEq_mul` (precise mul ultrametric), `valEq_neg` |
| `Hensel.lean` | Inverse: `invDigit0` (Bezout), `invSeq` / `invFull`, `mul_invSeq_correct` / `mul_invFull_correct`, `inv_trunc_unique`, `mul_left_cancel_trunc` / `mul_right_cancel_trunc`.  Sqrt: `SqrtBase`, `sqrtSeq` / `sqrtFull`, `sqr_sqrtSeq_correct` / `sqr_sqrtFull_correct`, `sqr_unique_trunc`, `sqrtFull_eq_of_sqr`.  Concrete: `i_5`, `i_13`, `sqrt_two_7` |
| `Teichmuller.lean` | `sum_geo_pow` (ZpSeq geometric sum), `frobenius_lift` (`y ≡ z mod p^k → y^p ≡ z^p mod p^(k+1)`, any `p ≥ 1`), `teichmuller_iter_cauchy` (iteration is Cauchy in p-adic metric); Nat-level engine `pow_add_factor` + `geo_sum_mod_zero_at_p` + `frobenius_lift_nat` (binomial-free) |
| `Field.lean` | `QpSeq` (num + shift), `QpSeq.{add,sub,mul,neg,ofNat}`, `QpSeq.inv` (Hensel via `invFull` + `shiftLeft`), `QpSeq.div`, `QpSeq.sqrt` (even-shift only — `√p ∉ ℚ_p`) + `sqr_sqrt_num_correct` |
| `DRLT.lean` | `canonical_5adic_NU` (5^25 in base 5), `canonical_5adic_p` (= 5), digit smokes, `canonical_5adic_NU_trunc_le_25` (DRLT anchor: first 25 levels zero) |

## Narrative

### Why infinite digit sequences

A p-adic integer is, classically, an element of the inverse limit
`lim_n ℤ/p^n`.  Operationally, this is an infinite stream of
digits in `{0, …, p-1}` — the residue at level `n` is recovered
by truncating to the first `n` digits.

In Lean, this is the natural ∅-axiom representation:
```lean
abbrev ZpDigit (p : Nat) : Type := Fin p
structure ZpSeq (p : Nat) where
  digits : Nat → ZpDigit p
```

The truncation `x.trunc n := Σ_{k<n} (x.digits k).val · p^k` is
a Nat in `[0, p^n)`.  The bound `trunc_lt_p_pow` is structural:
`x.trunc n < p^n` for `0 < p`.

The equivalence `eq_mod_pn_iff_trunc`:
```
(∀ k, k < n → x.digits k = y.digits k) ↔ x.trunc n = y.trunc n
```
confirms that truncation is the canonical projection
`ZpSeq → ℤ/p^n` — equality up to level n on either side detects
the same thing.

### Addition: the easy ring-quotient

For each position `k`, the digit sum
`(x.digits k).val + (y.digits k).val + carry k` splits as
`(digit, new carry)` via mod-p / div-p.  Recursive definition of
`Zp.carry` and `Zp.add`.

The **structural identity**:
```
x.trunc n + y.trunc n = (Zp.add x y).trunc n + Zp.carry n · p^n
```
(`add_trunc_eq`) cascades the digit-wise FSM steps into a single
Nat-level equation.  Taking both sides mod `p^n` and observing
that `carry n · p^n` vanishes mod `p^n` (`add_mul_mod_self_pure`),
plus `(Zp.add x y).trunc n < p^n` from the bound, yields the
**additive ring-quotient theorem**:
```lean
Zp.add_trunc : (Zp.add x y).trunc n = (x.trunc n + y.trunc n) % p^n
```

### Multiplication: the hard ring-quotient

The digit-by-digit multiplication is a **convolution with carry**:
position k's raw sum is
`mulRaw k = Σ_{i+j=k} x.digits i · y.digits (k-i)`,
plus accumulated carries.  The same FSM pattern as addition, but
each level mixes multiple lower terms.

The structural identity `mulSumRaw_eq_trunc` mirrors
`add_trunc_eq`, but the "raw sum equals truncation plus carry"
formulation alone is insufficient: we also need to relate
`mulSumRaw n` to `(x.trunc n · y.trunc n)`.

The **bridge** is a 9-step decomposition through the
**bilinear sum** `bilinSum p x y n n = x.trunc n · y.trunc n`
(`colSum_eq` + `bilinSum_eq`), splitting each row of the
n × n square at the diagonal cutoff (`colSum_split` via
`extColSum_eq_offDiagRow`), summing rows (`bilinSum_decomp` via
`diagSum`), level-extending the diagonal sum
(`diagSum_succ_level` + `diagSum_eq_mulSumRaw`), and finally
collapsing the off-diagonal contribution (a multiple of `p^n`)
via `add_mul_mod_self_pure`.

The result is the **multiplicative ring-quotient theorem**:
```lean
Zp.mul_trunc : (Zp.mul x y).trunc n = (x.trunc n · y.trunc n) % p^n
```

This is a non-trivial closure — the proof spans 9 named lemmas
across roughly 200 Lean lines.

### Hensel-lifted inverse

For `x : ZpSeq p` with `(x.digits 0).val` coprime to `p`
(witnessed by `(modBezout (x.digits 0).val p).1 = 1`), the
inverse `x^{-1} ∈ ℤ_p` is constructed by **Hensel lifting**:

- **Digit 0**: the modular Bezout inverse `invDigit0`,
  satisfying `(x.digits 0).val · invDigit0 ≡ 1 (mod p)`.
- **Digit `n+1`** (extension): given the current approximation
  `invSeq n` with `x · invSeq n ≡ 1 (mod p^(n+1))`, compute the
  error `e_n := ((x · invSeq n).digits (n+1)).val` and set the
  next digit to `negMod p (e_n · invDigit0)`.

`invSeq n : ZpSeq p` is built recursively, level by level.  At
each step, digits 0..n are correctly set; digits beyond n are 0
(by `invSeq_digit_above`).

The **general correctness theorem**:
```lean
Zp.mul_invSeq_correct (hp : 1 < p) :
    ∀ n, (Zp.mul x (invSeq n)).trunc (n + 1) = 1
```

Proof: induction on n.  Base case is `mul_invTemplate_trunc_one`
(level-1 from the Bezout identity).  The inductive step
`hensel_step` is the most elaborate proof in the library — a
~60-line chain combining `mul_trunc`, `invSeq_succ_trunc_extend`,
`add_mod_gen`, `mul_pow_succ_mod`, `hensel_cancel`, and
`hensel_final`.

The key fact `hensel_cancel`:
```
(e + x_0 · negMod p (e · i0) % p) % p = 0
```
encodes the Hensel correction: multiplying the error by
`(-invDigit0)` mod p produces exactly the digit that, when added
at position `p^(n+1)`, restores `x · y ≡ 1 mod p^(n+2)`.

### Propositional valuation

The p-adic valuation `v_p(x)` is the index of `x`'s first nonzero
digit.  Rather than introducing `WithTop ℕ` (which brings
typeclass machinery and axiom cost), `Norm.lean` uses a
**propositional** formulation:

```lean
def Zp.valAtLeast {p : Nat} (x : ZpSeq p) (n : Nat) : Prop :=
  ∀ k, k < n → (x.digits k).val = 0
```

Equivalent to `x.trunc n = 0` via `valAtLeast_iff_trunc`.  The
**exact** valuation
`valEq x n := valAtLeast x n ∧ (x.digits n).val ≠ 0` admits a
unique-value theorem `valEq_unique`.

### ℚ_p as ℤ_p[1/p]

```lean
structure QpSeq (p : Nat) where
  num : ZpSeq p
  shift : Nat
```

The pair `(num, shift)` represents `num · p^(-shift)`.
Multiplication is straightforward (`shift` adds).  Addition
aligns shifts via `Zp.shiftLeft` (multiplication by `p^k` on
ZpSeq).  Negation preserves the shift.

### DRLT integration

The DRLT resolution lattice uses `N_U = 5^25 = d^(d²)` (at
fractal level 2; `d = 5`).  The 5-adic Real213 picks up at the
resolution limit: `canonical_5adic_NU := digits_of_nat 5 (5^25)`
has digit 25 = 1 and all other digits = 0 — consistent with the
base-5 representation of `5^25`.

Whether the "infinite" 5-adic structure beyond the resolution
limit is operationally meaningful in DRLT, or is a formal
extension only, is itself a research question.  See
`seed/RESOLUTION_LIMIT_SPEC.md`.

## Key results

| Theorem | Lean module | Statement |
|---|---|---|
| `Zp.trunc_lt_p_pow` | `Foundation` | `x.trunc n < p^n` |
| `Zp.eq_mod_pn_iff_trunc` | `Foundation` | digit-wise agreement ↔ trunc-value agreement |
| `Zp.add_trunc` | `Arith` | `(x + y).trunc n = (x.trunc n + y.trunc n) % p^n` |
| `Zp.add_complement_digit` | `Arith` | every digit of `x + complement x` is `p − 1` |
| `Zp.mul_trunc` | `Arith` | `(x · y).trunc n = (x.trunc n · y.trunc n) % p^n` |
| `Zp.bilinSum_eq_mulSumRaw_plus_offDiag` | `Arith` | structural off-diagonal decomposition |
| `Zp.valEq_unique` | `Norm` | p-adic valuation is unique |
| `Zp.mul_invSeq_correct` | `Hensel` | `(x · invSeq n).trunc (n+1) = 1` (Hensel correctness) |
| `Zp.invDigit0_eq` | `Hensel` | `(x.digits 0).val · invDigit0 ≡ 1 (mod p)` (Bezout base) |
| `Zp.add_trunc_comm` | `Arith` | additive commutativity at trunc |
| `Zp.mul_trunc_comm` | `Arith` | multiplicative commutativity at trunc |
| `Zp.add_trunc_assoc` | `Arith` | additive associativity at trunc |
| `Zp.mul_trunc_assoc` | `Arith` | multiplicative associativity at trunc |
| `Zp.mul_add_trunc` / `Zp.add_mul_trunc` | `Arith` | distributivity at trunc |
| `QpSeq.add_shift` | `Field` | shift of `a + b` is `max a.shift b.shift` |
| `ZpSeq.digits_of_nat_trunc` | `Foundation` | `(digits_of_nat p hp m).trunc n = m % p^n` |
| `canonical_5adic_NU_trunc_le_25` | `DRLT` | `∀ n ≤ 25, canonical_5adic_NU.trunc n = 0` (DRLT anchor) |
| `Zp.invFull` + `mul_invFull_correct` | `Hensel` | full single-`ZpSeq` inverse, `x · x⁻¹ ≡ 1 (mod p^(n+1))` |
| `Zp.sqrtSeq` + `sqr_sqrtSeq_correct` | `Hensel` | Hensel sqrt iteration, `(sqrtSeq n)² ≡ x (mod p^(n+1))` |
| `Zp.sqrtFull` + `sqr_sqrtFull_correct` | `Hensel` | full single-`ZpSeq` sqrt |
| `Zp.i_5` + `i_5_sq_trunc_one/two` | `Hensel` | `i₅ = √(-1) ∈ ℤ_5`, with explicit digits 2,1,2,1,... |
| `Zp.valAtLeast_add` | `Norm` | additive ultrametric inequality |
| `Zp.valAtLeast_mul` | `Norm` | multiplicative ultrametric `val(xy) = val(x) + val(y)` |
| `Zp.valEq_add_of_lt` | `Norm` | strong additive: differing valuations → min dominates |
| `QpSeq.inv` / `QpSeq.div` | `Field` | inverse and division on ℚ_p |
| `QpSeq.sqrt` + `sqr_sqrt_num_correct` | `Field` | ℚ_p sqrt (even-shift only — `√p ∉ ℚ_p`) |
| `Zp.pow` + `pow_trunc` | `Pow` | natural-number power with trunc compatibility |
| `Zp.pow_add_trunc`, `Zp.pow_mul_trunc` | `Pow` | pow is a ring homomorphism at trunc |
| `Zp.pow_p_trunc_one` | `Pow` | Fermat at digit-0: `x^p ≡ x (mod p)` |
| `Zp.pow_p_minus_one_trunc_one` | `Pow` | Fermat: `x^(p-1) ≡ 1 (mod p)` for x unit |
| `Zp.teichmuller_iter` + invariant | `Pow` | iterate `x ↦ x^p`; digit-0 preserved mod p |
| `Zp.valAtLeast_pow` | `Pow` | `val(x^k) ≥ k · val(x)` (pow scales valuation) |
| `Zp.add_neg_self_trunc` | `Arith` | `(x + (-x)).trunc (n+1) = 0` — additive inverse |
| `Zp.sub_eq_zero_of_trunc_eq` / converse | `Arith` | `(a + (-b)).trunc = 0 ↔ a.trunc = b.trunc` |
| `Zp.inv_trunc_unique` | `Hensel` | Hensel inverse uniqueness |
| `Zp.mul_left_cancel_trunc` / right | `Hensel` | unit-mul cancellation at trunc |
| `Zp.mul_eq_zero_of_unit_left` | `Hensel` | unit times zero gives zero |
| `Zp.sqr_unique_trunc` | `Hensel` | Hensel sqrt uniqueness (matching digit 0) |
| `Zp.sqrtFull_eq_of_sqr` | `Hensel` | sqrtFull is THE Hensel sqrt |
| `Zp.valAtLeast_neg` | `Norm` | `val(-x) ≥ val(x)` — negation preserves valuation |
| `Zp.valEq_neg` | `Norm` | `val(-x) = val(x)` (precise) |
| `Zp.valEq_mul` | `Norm` | `val(xy) = val(x) + val(y)` (precise mul ultrametric) |
| `Zp.frobenius_lift` | `Teichmuller` | `y ≡ z mod p^k, k ≥ 1 → y^p ≡ z^p mod p^(k+1)` |
| `Zp.teichmuller_iter_cauchy` | `Teichmuller` | iter is Cauchy: `iter x (n+1) ≡ iter x n mod p^(n+1)` |

## Hensel infrastructure

The Hensel inverse and square root share a common template:

**Inverse**: given `x` with `(x.digits 0)` coprime to `p` (encoded
via Bezout: `h_gcd : (modBezout x_0 p).1 = 1`), iteratively build
`invSeq n` such that `x · invSeq n ≡ 1 (mod p^(n+1))`.  Diagonal
extraction `invFull.digits k := (invSeq k).digits k` collects
"settled" digits into the actual `ZpSeq` inverse.

**Square root**: given `Zp.SqrtBase p x` (a witness package:
`d_0` with `d_0² ≡ x.digits 0 mod p`, plus modular inverse of
`2·d_0`), iteratively build `sqrtSeq n` such that
`(sqrtSeq n)² ≡ x (mod p^(n+1))`.  Same diagonal trick yields
`sqrtFull`.  The algebraic core `sqrt_cancel_full` handles the
binomial-mod-`p^(n+2)` expansion and the `(err + 2·a·d) ≡ 0 mod p`
cancellation via `sqrt_cancel`.

**Algebraic engine** for the sqrt step:
1. `binomial_sq_mod_pure`: `(a + d·K)² mod M = (a² + 2·a·d·K) mod M`
   given `K² mod M = 0` (`K = p^(n+1)`, `M = p^(n+2)`).
2. `mod_eq_from_neg_eq`: lift `(Z + (M - xt)) % M = 0` to `Z % M = xt`.
3. `sqrt_cancel`: derive `(err + 2·a·d) % p = 0` from negMod_cancel +
   `2·d_0·two_d_0_inv ≡ 1 mod p` + `a ≡ d_0 mod p`.
4. `mul_pow_succ_mod`: lift mod-`p` cancellation to mod-`p^(n+2)`.

**Concrete 5-adic √(-1)**: `Zp.i_5 := sqrtFull 5 neg_one
sqrtBase_neg_one_5` with `sb.d_0 = 2`, `sb.two_d_0_inv = 4`.  The
Hensel iteration produces digits `2, 1, 2, 1, ...`, encoding
`i₅ = 2 + 5 + 2·25 + 125 + ... ∈ ℤ_5`.  Hard truth: -1 is a
quadratic residue mod 5, so ℤ_5 contains an "imaginary unit"
not present in ℝ.

## Ultrametric structure

The p-adic norm satisfies the non-Archimedean (ultrametric)
inequality:

- **Additive**: `val(x + y) ≥ min(val(x), val(y))` — in `valAtLeast`
  form, `valAtLeast x n ∧ valAtLeast y n → valAtLeast (x + y) n`.
- **Multiplicative**: `val(x · y) = val(x) + val(y)` — in `valAtLeast`
  form, `valAtLeast x m ∧ valAtLeast y n → valAtLeast (x · y) (m + n)`.

The multiplicative proof uses `trunc_extension_mod`: extending
trunc beyond level `m` preserves `% p^m`, so if `x.trunc m = 0`
then `x.trunc (m+k) = p^m · A` for some `A`.  Pairing with the
analogous y-side identity, the product is `p^(m+n) · (A·B)`,
divisible by `p^(m+n)`.

## Teichmüller convergence

The map `x ↦ x^p` defines `Zp.teichmuller_iter x n := x^(p^n)`.

**Digit-0 invariant** (Fermat at digit level): for p prime,
  `(teichmuller_iter x n).trunc 1 = x.trunc 1`  ∀n.

**Cauchy property** (`Zp.teichmuller_iter_cauchy`):
  `(iter x (n+1)).trunc (n+1) = (iter x n).trunc (n+1)`.

So the sequence agrees with itself at progressively deeper trunc
levels.  In the classical picture this says `x, x^p, x^(p²), …`
converges p-adically to the Teichmüller representative `ω(x)` —
the unique element with `ω(x) ≡ x (mod p)` satisfying `ω(x)^p =
ω(x)`.

### Frobenius lift (the engine)

`Zp.frobenius_lift`:
  `y ≡ z (mod p^k), k ≥ 1 → y^p ≡ z^p (mod p^(k+1))`.

Proved at trunc level via `pow_trunc` + digit decomposition +
the Nat-level lemma `frobenius_lift_nat`:
  `b ≡ 0 (mod p^k), k ≥ 1 → (a + b)^p ≡ a^p (mod p^(k+1))`.

The Nat-level proof uses the **geometric sum factorization**
  `(a + b)^p = a^p + b · S`  where  `S = ∑ᵢ₌₀ᵖ⁻¹ (a+b)ⁱ · aᵖ⁻¹⁻ⁱ`,
then observes `S ≡ 0 (mod p)` whenever `b ≡ 0 (mod p)` (each of
the p terms reduces to `aᵖ⁻¹ mod p`, total ≡ 0 by `p · k ≡ 0`).

Notably **the proof avoids binomial coefficients entirely** and
**does not require p to be prime**.  Frobenius lift holds for any
`p ≥ 1`, with the standard "binomial coefficients are divisible
by p" fact replaced by the "p terms each ≡ same value mod p"
identity.  Primality enters only at the digit-0 step (Fermat) when
we invoke `pow_p_trunc_one` for the base case of the Cauchy
induction.

## Closing reflection

What the Real213-p-adic campaign produced:

**Frontier results (all ∅-axiom)**:
- Full ring structure on `ZpSeq` (trunc level): add/mul/neg with
  comm, assoc, distrib, additive inverse axiom.
- Hensel lift for inverse and square root: both existence
  (`invFull`, `sqrtFull`) and uniqueness (`inv_trunc_unique`,
  `sqr_unique_trunc`) at every trunc level.
- p-adic norm with full strong ultrametric (additive + multiplicative,
  precise `valEq` versions).
- ℚ_p as the localization of `ℤ_p` at `p`: add, sub, mul, neg, inv,
  div, sqrt (the latter with the even-shift restriction since
  `√p ∉ ℚ_p`).
- Frobenius lift and Teichmüller iteration's Cauchy property —
  the deepest structural fact about iterated p-th powers.
- Three concrete p-adic algebraic numbers: `i₅ = √(-1) ∈ ℤ_5`,
  `i₁₃ = √(-1) ∈ ℤ_13`, `√2 ∈ ℤ_7`.  All built from `sqrtFull`
  applied to explicit `SqrtBase` instances.
- DRLT anchor: `canonical_5adic_NU` with full `trunc_le_25` zero
  attestation, bridging the finite resolution lattice to the
  5-adic envelope.

**What was surprising along the way**:

1. **Binomial-free Frobenius**.  The textbook proof of
   `y ≡ z (mod p^k) → y^p ≡ z^p (mod p^(k+1))` uses
   `p ∣ C(p, i)` for `0 < i < p` (p prime).  Our 213-native proof
   replaces this with the elementary observation that the
   geometric sum `∑ᵢ₌₀ᵖ⁻¹ (...)` has exactly `p` summands that
   are pairwise equal mod p, so its total mod p is `0` by the
   trivial identity `p · k ≡ 0 (mod p)`.  No primality, no
   binomial coefficients.  Just `1 · X + 1 · X + ⋯ + 1 · X = p · X`.

2. **Hensel-style uniqueness via cancellation**.  The Hensel
   inverse uniqueness, sqrt uniqueness, and the auxiliary
   cancellation laws (`mul_left_cancel_trunc`, `mul_right_cancel_trunc`,
   `mul_eq_zero_of_unit_left`) all stem from one observation:
   left-multiplying by `invFull x` is a bijection at trunc level
   when `x` is a unit.  The same one-liner argument carries to
   `(y + z) · (y − z) ≡ 0 ⟹ y ≡ z` (sqrt uniqueness via the
   abstract `sqrt_unique_digit_step`).

3. **Concrete vs. abstract**.  `i₅ = 2 + 5 + 2·25 + 125 + …` is a
   genuine 5-adic integer with a digit expansion that you can
   `#eval` and verify by hand.  Its construction goes through the
   same `sqrtFull` machinery as the abstract uniqueness theorem;
   no special-case code, no decide-based shortcut.  The library
   uniformly handles "compute" and "prove".

**What the campaign didn't do**:

- Promote ring laws to the digit (sequence-level) layer.  All ring
  axioms are at the `.trunc n` level only.  Lifting to the actual
  `ZpSeq` would require either a quotient construction (and
  propext / Quot.sound for `ZpSeq` equality up to trunc) or a
  convolution-style reindexing argument for `mulRaw_comm`.  Either
  would push us outside the strict-∅ guarantee.

- Construct the Teichmüller representative `ω(x)` as a concrete
  `ZpSeq`.  We have Cauchy convergence, but the limit object (the
  fixed point of the iteration in the inverse limit) requires
  either a completion construction or explicit digit extraction
  via diagonal stabilization (analog of `sqrtFull` for the
  iteration).  This is plausible follow-up work.

- Bridge to representations of the multiplicative group `ℤ_p^×`.
  We have the building blocks (unit predicate via `modBezout`,
  Fermat at digit 0, Teichmüller Cauchy) but not the structural
  isomorphism `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`.

**Methodology note**.  Most proofs in `Teichmuller.lean` and
`Hensel.lean` look like a sequence of `rw` over `mul_trunc`,
`add_trunc`, `mul_pow_succ_mod`, `mul_mod_pure`, etc., with
careful attention to *associativity choices* (`mul_assoc` vs.
`mul_left_comm`) and *which subterm of a goal the rewrite
matches*.  The `congrArg` workaround for `rw [b_eq]` mass-
substituting `b` inside `geo_sum_nat a b p` is a good example —
in a propext-permissive world you'd use `simp only [hb_eq]` with
a position restriction; in 213-pure you write `congrArg (· * S) hb_eq`
explicitly.

This is what 213-native proof engineering looks like at the
"medium-difficulty mathematical structure" scale: theorems that
would be one-liners in Mathlib become 50–200 line proofs here,
but they ship with a true ∅-axiom certificate.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Padic
python3 tools/scan_axioms.py E213.Lib.Math.Padic.Foundation \
                              E213.Lib.Math.Padic.Arith \
                              E213.Lib.Math.Padic.Pow \
                              E213.Lib.Math.Padic.Norm \
                              E213.Lib.Math.Padic.Hensel \
                              E213.Lib.Math.Padic.Teichmuller \
                              E213.Lib.Math.Padic.Field \
                              E213.Lib.Math.Padic.DRLT
# Expected: 308 PURE / 0 DIRTY
```
