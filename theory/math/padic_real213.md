# Real213-p-adic — 213-native p-adic Numbers

**Status**: Closed (26 files, ~462 PURE).

## Overview

**Real213-p-adic** is a 213-native, ∅-axiom construction of the
p-adic integers `ℤ_p` and p-adic numbers `ℚ_p`.  The library is
organised in eight modules:

- **Foundation** — `ZpSeq p` as an infinite digit sequence
  `ℕ → Fin p`, with truncation `trunc : ℕ → ℕ` faithfully
  embedding into `ℤ/p^n`.
- **Arith** — `add`, `mul`, `neg` defined digit-by-digit via carry
  FSMs; the central ring-quotient theorems `add_trunc`, `mul_trunc`
  state that truncation is a ring homomorphism; full ring axioms
  at trunc (commutativity, associativity, distributivity, additive
  inverse `add_neg_self_trunc`).
- **Pow** — natural-number power `Zp.pow x n` with homomorphism
  properties at trunc; Fermat's little theorem at digit 0
  (`pow_p_trunc_one`, requires p prime); `teichmuller_iter`.
- **Norm** — propositional valuation `valEq` with full strong
  ultrametric: additive `valEq_add_of_lt`, multiplicative
  `valEq_mul`, and negation `valEq_neg`.
- **Hensel** — both inverse and square root, each with existence
  (`invFull`, `sqrtFull`) and uniqueness (`inv_trunc_unique`,
  `sqr_unique_trunc`) at every trunc level.  Concrete instances:
  `i_5 = √(-1) ∈ ℤ_5`, `i_13 ∈ ℤ_13`, `√2 ∈ ℤ_7`.
- **Teichmüller** — Frobenius lift `y ≡ z (mod p^k) → y^p ≡ z^p
  (mod p^(k+1))` (any `p ≥ 1`) and Cauchy convergence of the
  iteration `x ↦ x^p`.
- **Field** — ℚ_p as `QpSeq` with add/sub/mul/neg/inv/div/sqrt.
- **DRLT** — canonical 5-adic embeddings (`ℕ ↪ ZpSeq 5`), e.g. the
  lift of the base prime `5`, with digit smoke-tests.

The library is ∅-axiom throughout: every theorem reports
`#print axioms … → "does not depend on any axioms"`.  Mathlib's
`Padic` builds on Cauchy completion which brings `propext`,
`Quot.sound`, `Classical.choice`; Real213-p-adic brings none.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberSystems/Padic/` (8 files)
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
| `DRLT.lean` | `canonical_5adic_p` (= 5) + digit smokes, `canonical_5adic_zero` (canonical 5-adic embeddings) |

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

### Canonical 5-adic embeddings

The 5-adic Real213 gives a canonical embedding `ℕ ↪ ZpSeq 5` for
any natural number via `digits_of_nat`.  For instance the lift of
the base prime, `canonical_5adic_p := digits_of_nat 5 5`, has
digit 1 = 1 and all other digits = 0.  `configCount 2 = 5^25` is
a bare arithmetic value; no fractal level is a resolution limit.

Whether the "infinite" 5-adic structure beyond the resolution
limit is operationally meaningful in DRLT, or is a formal
extension only, is itself a research question.  See
`seed/RESOLUTION_LIMIT_SPEC.md`.

## Key results

Grouped by module.

**Foundation**
| Theorem | Statement |
|---|---|
| `Zp.trunc_lt_p_pow` | `x.trunc n < p^n` |
| `Zp.eq_mod_pn_iff_trunc` | digit-wise agreement ↔ trunc-value agreement |
| `ZpSeq.digits_of_nat_trunc` | `(digits_of_nat p hp m).trunc n = m % p^n` |

**Arith** (ring axioms at trunc level)
| Theorem | Statement |
|---|---|
| `Zp.add_trunc`, `Zp.mul_trunc` | trunc is a ring homomorphism `ZpSeq → ℤ/p^n` |
| `Zp.bilinSum_eq_mulSumRaw_plus_offDiag` | off-diagonal decomposition (`mul_trunc` engine) |
| `Zp.add_trunc_comm` / `assoc`, `mul_trunc_comm` / `assoc` | commutative ring axioms at trunc |
| `Zp.mul_add_trunc` / `add_mul_trunc` | distributivity |
| `Zp.add_neg_self_trunc` | additive inverse axiom |
| `Zp.sub_eq_zero_of_trunc_eq` / converse | biconditional difference-is-zero |

**Pow**
| Theorem | Statement |
|---|---|
| `Zp.pow_trunc` | `(x^n).trunc m = (x.trunc m)^n % p^m` |
| `Zp.pow_add_trunc`, `Zp.pow_mul_trunc` | exponent + base homomorphism |
| `Zp.pow_p_trunc_one` | Fermat: `x^p ≡ x (mod p)` (p prime) |
| `Zp.pow_p_minus_one_trunc_one` | Fermat: `x^(p−1) ≡ 1 (mod p)` for x a unit |
| `Zp.teichmuller_iter` + digit-0 invariant | iterate `x ↦ x^p` |
| `Zp.valAtLeast_pow` | `val(x^k) ≥ k · val(x)` |

**Norm**
| Theorem | Statement |
|---|---|
| `Zp.valEq_unique` | p-adic valuation is unique |
| `Zp.valAtLeast_add`, `valEq_add_of_lt` | additive ultrametric (≥ and strong forms) |
| `Zp.valAtLeast_mul`, `valEq_mul` | multiplicative ultrametric `val(xy) = val(x) + val(y)` |
| `Zp.valAtLeast_neg`, `valEq_neg` | negation preserves valuation |

**Hensel** — inverse + sqrt with existence + uniqueness
| Theorem | Statement |
|---|---|
| `Zp.invDigit0_eq` | digit-0 inverse via Bezout |
| `Zp.mul_invFull_correct` | `x · invFull x ≡ 1 (mod p^(n+1))` (existence) |
| `Zp.inv_trunc_unique` | inverse uniqueness at trunc |
| `Zp.mul_left_cancel_trunc` / right, `mul_eq_zero_of_unit_left` | unit cancellation laws |
| `Zp.sqr_sqrtFull_correct` | `(sqrtFull x sb)² ≡ x (mod p^(n+1))` (existence) |
| `Zp.sqr_unique_trunc`, `sqrtFull_eq_of_sqr` | sqrt uniqueness, `sqrtFull` is THE sqrt |
| `Zp.i_5`, `Zp.i_13`, `Zp.sqrt_two_7` | concrete p-adic algebraic numbers |

**Teichmuller**
| Theorem | Statement |
|---|---|
| `Zp.frobenius_lift` | `y ≡ z mod p^k, k ≥ 1 → y^p ≡ z^p mod p^(k+1)` (any `p ≥ 1`) |
| `Zp.teichmuller_iter_cauchy` | `iter x (n+1) ≡ iter x n (mod p^(n+1))` |

**Field** (ℚ_p)
| Theorem | Statement |
|---|---|
| `QpSeq.{add,sub,mul,neg}` | basic arithmetic |
| `QpSeq.inv`, `QpSeq.div` | Hensel-based inverse and division |
| `QpSeq.sqrt` + `sqr_sqrt_num_correct` | sqrt (even-shift only — `√p ∉ ℚ_p`) |

**DRLT**
| Theorem | Statement |
|---|---|
| `canonical_5adic_p_digit_1` | base-prime lift: digit 1 of `5` in base 5 is `1` |

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
- Canonical 5-adic embeddings: the lift of the base prime `5`
  (`canonical_5adic_p`) with digit smoke-tests.

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

## Cross-reference — Möbius P-orbit mod-p periods

The p-adic family `ZpSeq p` is parametrised by ANY prime `p`, making
it the natural Lens-arena for mod-p reductions of the Möbius matrix
`P = [[2,1],[1,1]]`.  This connection is formalised in two layers:

  · **Lean bridge**: `Lib/Math/NumberSystems/Padic/ZpSeqMobiusBridge.lean` defines
    `ZpMobiusPairEq` (digit agreement at every Stern-Brocot reachable
    pair) and proves bidirectional equivalence with `ZpSeqEquiv` —
    the canonical p-adic setoid.  This shows the Möbius-pair reading
    of p-adic equality is tight (neither weaker nor stronger).
  · **Orbit-period link**: for each prime `p`, the Möbius period
    `T_p = ord(P mod p)` is the minimal cycle length of `P` in
    `GL(2, F_p)`.  The p-adic digit carry FSM and truncation
    homomorphism (`add_trunc`, `mul_trunc`) operate at `mod p^n`
    levels; the period `T_p` emerges at `n = 1` as the fundamental
    residue cycle.  The Lucas-Pell trace `L(k) = trace(P^k)` at
    any `k < T_p` gives a non-trivial digit-zero Teichmüller seed.
  · **Framework significance**: the fact that `ZpSeq p` exists for
    ANY `p` (not just atomic primes 2, 3, 5) is what makes mod-13
    and mod-29 period computations (`T_13 = 14`, `T_29 = 7`)
    framework-natural despite their non-atomic factors — the p-adic
    Lens family is already general.

See [`theory/math/mobius213_p_orbit_closure.md`](mobius213_p_orbit_closure.md)
for the full mod-p period catalog and the P-orbit closure ring.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.NumberSystems.Padic
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Padic.Foundation \
                              E213.Lib.Math.NumberSystems.Padic.Arith \
                              E213.Lib.Math.NumberSystems.Padic.Pow \
                              E213.Lib.Math.NumberSystems.Padic.Norm \
                              E213.Lib.Math.NumberSystems.Padic.Hensel \
                              E213.Lib.Math.NumberSystems.Padic.Teichmuller \
                              E213.Lib.Math.NumberSystems.Padic.Field \
                              E213.Lib.Math.NumberSystems.Padic.DRLT
# Expected: 308 PURE / 0 DIRTY
```
