# Real213-p-adic — 213-native p-adic Numbers

**Status**: Closed (6 files, 207 PURE).

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

- **Sub-tree**: `lean/E213/Lib/Math/Padic/` (6 files)
- **Umbrella**: `Padic.lean`
- **∅-axiom status**: 207 PURE / 0 DIRTY

### Sub-cluster organization

| File | Topic |
|---|---|
| `Foundation.lean` | `ZpDigit`, `ZpSeq`, `trunc`, `zero`, `one`, `neg_one`, `eq_mod_pn`, `trunc_lt_p_pow`, `eq_mod_pn_iff_trunc`, `digits_of_nat`, `trunc_neg_one_succ`, `trunc_one_succ` |
| `Arith.lean` | `Zp.carry`, `Zp.add`, `Zp.add_trunc_eq`, `Zp.add_trunc`, `Zp.complement`, `Zp.neg`, `Zp.mul` + `mulRaw`/`mulCarry`, off-diagonal decomposition (`offDiagRow`, `offDiagSum`, `diagSum`), `Zp.mul_trunc` (general bridge), `Zp.shiftLeft` + trunc structure, identity/absorbing/commutativity laws at digit and trunc levels |
| `Norm.lean` | `Zp.valAtLeast`, `Zp.valAtLeast_mono`, `Zp.valAtLeast_iff_trunc`, `Zp.valEq`, `Zp.valEq_unique`, `valEq_one`, `valEq_neg_one` |
| `Hensel.lean` | `Zp.unit0`, `Zp.invDigit0` (Bezout), `Zp.invTemplate`, `Zp.invSeq` (Hensel-lifted full inverse), structural lemmas (`invSeq_succ_trunc_extend`, `invSeq_trunc_at_succ`, `invSeq_digit_above`, …), `Zp.negMod`, `Zp.mul_invSeq_correct` (general correctness) |
| `Field.lean` | `QpSeq` (numerator + shift), `QpSeq.mul` (shift-additive), `QpSeq.add` (shift-aligning via `Zp.shiftLeft`), `QpSeq.neg`, `QpSeq.sub`, `QpSeq.ofNat` |
| `DRLT.lean` | `canonical_5adic_NU` (= 5^25 in base 5), `canonical_5adic_p` (= 5), digit smokes at positions 0, 1, 2, 24, 25, 26 |

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

## Open frontier

- **Digit-level ring laws** (`mul_comm_digit`, `mul_assoc_digit`):
  trunc-level versions are closed (commutativity, associativity,
  distributivity).  Digit-level would require a convolution
  reindexing argument for `mulRaw x y k = mulRaw y x k`.
- **Hensel for square root**: the inverse construction generalizes
  to `Hensel_lift f f' a₀` for arbitrary polynomial `f`.  Not yet
  written.
- **DRLT anchor at higher levels**: `canonical_5adic_NU_trunc_le_25`
  closes the n ≤ 25 case.  Beyond level 25, the truncation
  recovers `5^25 % 5^n`, which is `5^25 - q · 5^n` for the
  appropriate quotient — not zero in general; this regime
  corresponds to "infinite precision beyond the resolution
  limit" (see `seed/RESOLUTION_LIMIT_SPEC.md`).
- **ℚ_p inverse / field structure**: `QpSeq` has add/mul/neg/sub
  but no general inverse yet (would need a Hensel-lifted
  `QpSeq.inv` using `Zp.invSeq` + shift bookkeeping).

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Padic
python3 tools/scan_axioms.py E213.Lib.Math.Padic.Foundation \
                              E213.Lib.Math.Padic.Arith \
                              E213.Lib.Math.Padic.Norm \
                              E213.Lib.Math.Padic.Hensel \
                              E213.Lib.Math.Padic.Field \
                              E213.Lib.Math.Padic.DRLT
# Expected: 207 PURE / 0 DIRTY
```
