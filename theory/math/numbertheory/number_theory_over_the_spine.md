# Elementary number theory generated over the Raw spine

**Status**: Closed (the full leg-2 discipline computed over the Raw-generated ℕ₊).
Mirrors `lean/E213/Lens/Number/Nat213/{Order, Divisibility, Irreducible,
EuclidUnique, Prime, Gcd, Coprime, WellOrder, Valuation, Factorization, FTA}.lean`.
Conceptual residue (Legs 1 & 3) stays open in `research-notes/frontiers/the_descent_leg.md`.

## Overview

`theory/math/numbersystems/naturals_from_the_spine.md` closed the **carrier**: ℕ₊ as a
reading of the distinguishing's `slash`-successor spine (`Nat213`, with its own
no-zero/no-subtraction Peano arithmetic, order, and recursion — Lean's `Nat` only as the
`depth` readout). This chapter closes the **discipline computed on that carrier**: an entire
elementary number theory — order, divisibility, gcd, coprimality, well-ordering,
exponentiation, primality, factorization, the Fundamental Theorem of Arithmetic, and the
`p`-adic valuation — *generated all the way down* over `Nat213`, with **no detour through
Lean's `Nat`** in the statements or the load-bearing proofs.

This is the descent leg's leg-2 made concrete: not a re-derivation of classical number theory
over a borrowed carrier, but the **same theorems obtained as facts about the distinguishing's
own counting object**. The shape of the discipline is *forced* by the primitive — divisibility
has a bottom (`one`, the atom) but no top (the count never closes), there is no absorbing zero,
and exponents carry no zero (a multiplicity, being a count, is read *out* into ℕ where `0`
lives — the legitimate Lens direction).

## Lean source

- Umbrella: `lean/E213/Lens/Number/Nat213.lean`
- Files (∅-axiom, 0 DIRTY):
  - `Order.lean` (222) — native strict total order `lt` + non-strict total partial order `le`;
    additive / multiplicative / power monotonicity; native cancellation; square-injectivity.
  - `Divisibility.lean` (160) — `Dvd` as a partial order with bottom `one`, no top;
    `dvd_imp_le`; power facts (`dvd_pow_self`, `pow_dvd_pow`, `self_dvd_pow`).
  - `Irreducible.lean` (172) — irreducibility; small-number enumeration helpers.
  - `EuclidUnique.lean` (142) — Euclid's lemma (`euclid`); subtractive gcd existence with the
    scaled multiplicative spec (`gcd_exists_mul`) — the Bézout substitute that fits ℕ₊ (no zero).
  - `Prime.lean` (71) — irreducible ⟺ prime (`irreducible_iff_prime`); `irreducible_dvd_pow_iff`.
  - `Gcd.lean` (108) — the gcd discipline (`IsGcd`): divisibility is a meet-semilattice
    (existence + uniqueness + the multiplicative law).
  - `Coprime.lean` (140) — coprimality (`Coprime a b := IsGcd a b one`): the coprime-division
    law, descent to divisors, multiplicative + power closure, the Prime↔Coprime bridge.
  - `WellOrder.lean` (53) — well-foundedness as a named API (`strong_induction`, `well_ordering`).
  - `Valuation.lean` (179) — the `p`-adic valuation, both forms (A: ℕ-readout `vp` with exactness;
    B: native `padic_factorization` with uniqueness).
  - `Factorization.lean` (196) — factorization existence; decidable `Dvd`; native well-foundedness.
  - `FTA.lean` (159) — the Fundamental Theorem of Arithmetic, generated over `Nat213`.
- ∅-axiom status: every theorem reports `#print axioms → "does not depend on any axioms"`.

## Narrative

### The order, all from `add`

The native strict order is the add-witness relation: `a < b` iff `b` is `a` with a positive
`Nat213` added (`Order.lt`, `def lt a b := ∃ c, add a c = b`). Because `Nat213` has no zero,
every added element is positive, so this is genuinely strict. From this single definition the
whole order theory falls out *algebraically* — irreflexivity from `add_ne_self`, transitivity
by composing witnesses, trichotomy by structural double recursion (`lt_trichotomy`), and the
monotonicities of `add`, `mul`, and `pow` from distributivity alone, with **no Lean `Nat` order
lemma** (which would pull `propext`/`Classical.choice`). Strict monotonicity of squaring
(`lt_mul_self`) yields square-injectivity (`mul_self_inj`); strict monotonicity of left
multiplication yields native cancellation (`mul_left_cancel`). The non-strict order
`le a b := a = b ∨ lt a b` is a total partial order (`le_total_order`).

### Divisibility, gcd, coprimality

`Dvd a b := ∃ c, b = mul a c` (on `Nat213`'s own `mul`) is a partial order with bottom `one`
(the atom-count floor) and **no top** (`dvd_no_top` — the count never closing forces openness
upward), refining the additive order (`dvd_imp_le`). Euclid's subtractive gcd — every step
subtracts the smaller from the larger, the difference being the `lt`-witness, so it lives in ℕ₊
with no zero remainder — gives gcd existence *and* the multiplicative law `gcd(c·a,c·b)=c·gcd(a,b)`
in one well-founded induction (`EuclidUnique.gcd_exists_mul`). Extracted, this makes divisibility
a **meet-semilattice** (`Gcd.IsGcd`, `gcd_meet_semilattice`): every pair has a unique greatest
common divisor. Coprimality (`Coprime a b := IsGcd a b one`) carries Euclid's coprime-division
law (`coprime_dvd_mul`), is closed under products and powers, and an irreducible is coprime to
exactly its non-multiples (`irreducible_coprime_iff`).

### Primality, factorization, FTA

Over `Nat213` the two notions of "prime" coincide — irreducible (no nontrivial factorization)
⟺ prime (`p∣a·b → p∣a ∨ p∣b`) — `Prime.irreducible_iff_prime`, the UFD-defining coincidence.
A prime dividing a power divides the base (`irreducible_dvd_pow`). Every `Nat213` is a product of
irreducibles (`Factorization.exists_factorization`, well-founded recursion on the native `lt` and a
*decided* irreducible/composite dichotomy — `decBoundedExists`, no `Classical`), and the
factorization is unique up to permutation: the **Fundamental Theorem of Arithmetic, generated over
the distinguishing's own counting object** (`FTA.fta`).

### Well-ordering and the `p`-adic valuation

`Nat213`'s well-foundedness (`WellOrder`, from structural `acc_lt`) is exposed as `strong_induction`
and a constructive `well_ordering` (every inhabited decidable predicate has a `lt`-minimal witness).
The `p`-adic structure resolves the **no-zero tension** (a valuation counts, and the count can be
zero, but `Nat213` has none) in the two complementary forms the carrier's shape dictates:

- **A — readout into ℕ.** The multiplicity is a count, so it reads *out* into ℕ — the legitimate
  Lens direction, exactly like `toNat`/`Raw.depth`. `Valuation.vp : Nat213 → Nat213 → Nat`, built on
  `Peano.powNat` (the `Nat`-exponent power, `powNat a 0 = one`, which `pow` cannot provide). The
  searched power genuinely divides (`pow_vp_dvd`), and `vp` is the **largest** such exponent
  (`le_vp_iff`: `p^k ∣ n ⟺ k ≤ vp p n`, for `p ≠ one`).
- **B — native factorization.** Fully `Nat213`-native, no readout: for a prime `p ∣ n` (so the
  exponent is ≥ 1, expressible in `Nat213`), `n = p^k · m` with `¬ p ∣ m`
  (`padic_factorization`), and the `(k,m)` is **unique** (`padic_factorization_unique`) — welding
  B's native exponent to A's `vp`.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `lt_strict_total_order`, `le_total_order` | `Order` | `lt`/`le` are total (partial) orders on ℕ₊, from `add` alone |
| `mul_self_inj`, `mul_left_cancel` | `Order` | square-injectivity + native cancellation (no `toNat`) |
| `dvd_antisymm`, `dvd_no_top` | `Divisibility` | `Dvd` is a partial order with bottom `one`, no top |
| `gcd_exists_mul` | `EuclidUnique` | subtractive gcd + multiplicative law, one induction, no zero |
| `gcd_meet_semilattice` | `Gcd` | divisibility is a meet-semilattice (gcd exists + unique) |
| `coprime_dvd_mul`, `coprime_pow`, `irreducible_coprime_iff` | `Coprime` | coprime-division law; power closure; Prime↔Coprime bridge |
| `irreducible_iff_prime` | `Prime` | irreducible ⟺ prime — the UFD coincidence |
| `fta` | `FTA` | the Fundamental Theorem of Arithmetic, generated over `Nat213` |
| `strong_induction`, `well_ordering` | `WellOrder` | ℕ₊ is well-ordered (constructive) |
| `le_vp_iff` | `Valuation` | `p^k ∣ n ⟺ k ≤ vp p n` — `vp` is the largest dividing exponent |
| `padic_factorization`(`_unique`) | `Valuation` | `n = p^k·m`, `¬p∣m`, for `p∣n` — exists and unique |

## Research-note provenance

`research-notes/frontiers/the_descent_leg.md` (the descent-leg frontier — leg-2 build-out section),
building on the carrier closed in `theory/math/numbersystems/naturals_from_the_spine.md` and the
native-`Nat` FTA grounding in `theory/math/numbertheory/grounded_fundamental_theorem.md`.

## Open frontier

The arithmetic is closed; the residue is **conceptual** and stays in
`research-notes/frontiers/the_descent_leg.md`:
- **Leg 1** — the carrier still borrows the kernel's `inductive` to *have* `Raw` and `Nat` as the
  `depth` readout (generated-vs-borrowed; conceded).
- **Leg 3** — no proof that the distinguishing primitive is non-interchangeable with rivals
  (forcing-vs-matching; the open middle of `the_one_act.md`).
- Minor: an `lcm` dual join (needs an upper bound; deferred).

## How to verify

```bash
cd lean && lake build E213.Lens.Number.Nat213
# axiom purity (per module, from repo root):
python3 tools/scan_axioms.py E213.Lens.Number.Nat213.Valuation
```
</content>
