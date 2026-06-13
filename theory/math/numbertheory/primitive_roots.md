# Primitive roots — `(ℤ/p)*` is cyclic, and Zolotarev the classical way

## Overview

For a prime `p`, the units mod `p` form a **cyclic** group: there is a
*primitive root* `g` whose powers `g⁰, g¹, …, g^{p−2}` exhaust `{1,…,p−1}`.
This chapter closes that existence ∅-axiom, from the multiplicative order
upward, and uses it to give the **classical** proof of Zolotarev's lemma —
`psign (x ↦ a·x mod p) = (a/p)` — via the primitive root being a single
`(p−1)`-cycle.  It supplies the cyclicity-of-units infrastructure that the
symmetric-cross-count proof in `zolotarev.md` needs no generator for; the two
routes to Zolotarev are independent and both ∅-axiom.

Nothing here is a continuous statement.  Order, max-order, the prime-power
splitting of an exponent, and "every order divides the maximum" are all
**counting** facts about the finite cyclic structure of `{1,…,p−1}`; the
primitive root is the witness that the count of distinct powers reaches its
ceiling `p−1`.

## Lean source

- Umbrella: `lean/E213/Lib/Math/NumberTheory/ModArith.lean`
- Multiplicative order: `ModArith/MulOrder.lean` (13 PURE), `OrderPow.lean`
  (4 PURE), `CoprimeOrder.lean` (1 PURE)
- Max order + exponent argument: `ModArith/MaxOrder.lean` (13 PURE),
  `ModArith/EveryOrdDvdMax.lean` (3 PURE)
- Valuation support: `Meta/Nat/Valuation.lean` (15 PURE),
  `ModArith/QPart.lean` (6 PURE), `ModArith/ValuationAlg.lean` (5 PURE),
  `NumberTheory/Lcm213.lean` (11 PURE)
- Primitive-root existence: `ModArith/PrimitiveRoot.lean` (9 PURE)
- Classical Zolotarev: `ModArith/ZolotarevReduction.lean` (4 PURE),
  `ModArith/ZolotarevCycle.lean` (47 PURE)
- ∅-axiom status: **0 DIRTY** throughout (every theorem
  `#print axioms → "does not depend on any axioms"`).

## Narrative

### The multiplicative order

For a unit `a` (`1 ≤ a < p`, `p ∤ a`), the **order** `ordModP a p` is the
least `k ≥ 1` with `aᵏ ≡ 1 (mod p)` (`MulOrder.ordModP`, found by the bounded
upward search `findOrd`).  It exists because Fermat's little theorem
(`fermat : a^{p−1} % p = 1`, wrapping `UniversalFLT`) caps the search at
`p−1`.  The defining facts:

- `pow_ord : a^{ordModP a p} % p = 1` and minimality `ord_min`;
- ★ `ord_dvd : aᵏ ≡ 1 ⟹ ordModP a p ∣ k` — the order divides *every*
  fixing exponent.  By the Euclidean split `k = ord·q + r`: the
  `a^{ord} ≡ 1` collapse (`pow_split_eq`) gives `aᵏ ≡ aʳ`, so `aʳ ≡ 1` with
  `r < ord` forces `r = 0` by minimality.
- `ord_dvd_p_sub_one : ordModP a p ∣ (p−1)` (Fermat as a special case).

Order interacts with powers and products:

- ★ `ord_pow : ordModP (aᵏ) p = ordModP a p / gcd(ordModP a p, k)`
  (`OrderPow`), the order of a power;
- ★ `ord_mul_coprime : gcd(ord a, ord b) = 1 ⟹ ordModP ((a·b)%p) p =
  ord a · ord b` (`CoprimeOrder`) — coprime orders multiply.  This is the
  combinatorial engine: it lets two elements of coprime order be *glued*
  into one of the product order.

The `lcm` machinery this needs (`Lcm213`: ℕ `lcm` with its universal
property `lcm_dvd` and `gcd_mul_lcm`, all **without Bézout**) and the `q`-adic
valuation (`Meta/Nat/Valuation.lean`: `vp q n` the largest `k` with `qᵏ ∣ n`;
`QPart`/`ValuationAlg`: `vp_mul`, and the extraction `exists_prime_vp_gt`)
are the supporting arithmetic.

### Every order divides the maximum

Let `maxOrd p` be the largest order among the units `[1, p−1]`
(`MaxOrder.maxOrd`), achieved by some unit `g` (`maxOrd_achieved`).  The
crux — the heart of cyclicity — is

> ★★★★ `every_ord_dvd_maxOrd : ordModP a p ∣ maxOrd p` for every unit `a`
> (`EveryOrdDvdMax`).

The proof is the **exponent argument**, ∅-axiom via a pure decidable
case-split (no Classical `by_contra`): if some `ord a ∤ maxOrd`, a prime `q`
divides `ord a` to a strictly higher power than it divides `maxOrd`
(`exists_prime_vp_gt`, routed through valuations + `gcd_div_coprime`).  Then
build `x = a^{ord a / A}` of order `A = q^{v_q(ord a)}` and
`y = g^{q^{v_q(maxOrd)}}` of order `B = maxOrd / q^{v_q(maxOrd)}`; `A, B` are
coprime (`gcd_qpow_qfree`), so `ord((x·y)%p) = A·B > maxOrd`
(`ord_mul_coprime`), contradicting maximality `maxOrd_ge`.  Glue two elements
whose orders' prime-power profiles dominate, and you exceed the supposed
maximum.

### The primitive root

`every_ord_dvd_maxOrd` says all `p−1` units satisfy `x^{maxOrd} ≡ 1`
(`pow_maxOrd_eq_one`).  So `X^{maxOrd} − 1` (over `ℤ`) has `p−1` distinct
roots — but a degree-`maxOrd` polynomial over the field `ℤ/p` has at most
`maxOrd` roots (`RootBound.eval_zero`).  Hence `p−1 ≤ maxOrd`; with
`maxOrd ∣ p−1` this forces

> ★★★ `maxOrd_eq_pred : maxOrd p = p − 1`     (`PrimitiveRoot`),

so the order-achiever is a generator:

> ★★★★ `exists_primitive_root : ∃ g, 1 ≤ g ≤ p−1 ∧ ordModP g p = p − 1`.

`(ℤ/p)*` is cyclic.  (The root-counting bound `RootBound.eval_zero` is the
same finite-field fact powering the Euler-criterion converse — here it caps
the number of solutions of `X^{maxOrd} = 1`.)

### Zolotarev the classical way

Multiplication by a unit `a` permutes `{0,…,p−1}`; its value-list is
`mulPerm a p = (iota p).map (·*a % p)` (`Zolotarev.lean`).  The **sign**
`psign σ := altSign (inversions σ)` is multiplicative in `a`
(`psign_mulPerm_hom`) and trivial on squares (`psign_mulPerm_qr`), so
`a ↦ psign (mulPerm a p)` is a `{±1}` character killing the residues.  To be
the Legendre symbol it must be *non-trivial* — one non-residue with sign
`−1` suffices, and the rest follows from the character law
(`ZolotarevReduction.zolotarev_iff`: given a single odd witness `a₀`, every
non-residue `a` has `a·a₀` a residue, forcing `psign (mulPerm a) = −1`).

The witness is the primitive root.  `mulPerm g` fixes `0` and is a single
`(p−1)`-cycle on the units; conjugating it to the standard rotation
`cycS = [0, p−1, 1, 2, …, p−2]` by the discrete-log list
`τ(i) = g^{p−1−i} mod p` gives

```
composeList (mulPerm g) τ = composeList τ cycS     (conj_eq),
```

so, `psign` being a class function (`psign_mul` + the `±1` self-cancel),
`psign (mulPerm g) = psign (cycS)`.  The standard rotation has exactly `p−2`
inversions (the ascending-block calculus `inversions_cycS`), and `p−2` is odd
for odd `p`, so `psign (cycS) = (−1)^{p−2} = −1` (`psign_cycS`).  A primitive
root is a non-residue (its order `p−1 = 2m` does not divide `m`,
`primitive_not_qr`), so it is exactly the odd witness, and

> ★★★★★ `zolotarev_full : psign (mulPerm a p) = 1 ⟺ a` is a QR mod `p`
> (`ZolotarevCycle`).

The conjugation rests on the discrete-log list being a permutation, which is
where cyclicity pays off: `τ` is injective because the powers `g⁰,…,g^{p−2}`
are distinct (`pow_inj_mod`, via `res_cancel` cancellation + `ord_dvd` with
`ord g = p−1` and periodicity `pow_period`).

This is the textbook proof — "a generator is a `(p−1)`-cycle of sign `−1`" —
made ∅-axiom.  It is independent of the symmetric-cross-count proof in
`zolotarev.md`; the value added here is the reusable `(ℤ/p)*`-cyclic
infrastructure, which that route never builds.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `ord_dvd` | `MulOrder` | `aᵏ ≡ 1 ⟹ ord a ∣ k` |
| `ord_mul_coprime` | `CoprimeOrder` | coprime orders multiply |
| `ord_pow` | `OrderPow` | `ord(aᵏ) = ord a / gcd(ord a, k)` |
| `every_ord_dvd_maxOrd` | `EveryOrdDvdMax` | every unit's order divides `maxOrd` |
| `maxOrd_eq_pred` | `PrimitiveRoot` | `maxOrd p = p − 1` |
| `exists_primitive_root` | `PrimitiveRoot` | `∃ g, ord g = p − 1` (cyclicity) |
| `psign_cycS` | `ZolotarevCycle` | the standard `(p−1)`-rotation is odd |
| `psign_mulPerm_primitive` | `ZolotarevCycle` | `psign (mulPerm g p) = −1` for a primitive root |
| `zolotarev_full` | `ZolotarevCycle` | `psign (mulPerm a p) = 1 ⟺ a` QR |

## Research-note provenance

The dependency spine builds upward in the order `MulOrder → Lcm213 →
OrderPow → CoprimeOrder → MaxOrder → Valuation/QPart/ValuationAlg →
EveryOrdDvdMax → PrimitiveRoot → ZolotarevReduction → ZolotarevCycle`.  The
Zolotarev converse it establishes is also closed independently by the
symmetric-cross-count route of `zolotarev.md`.

## Discrete-log readout of the quadratic character

The `(ℤ/p)*`-cyclic infrastructure pays off again in
`ModArith/DiscreteLogParity.lean`: the Legendre symbol is the **parity of the
discrete logarithm**.  For a primitive root `g`, `QR(g^k % p) ⟺ 2 ∣ k`
(`qr_pow_iff_even_exp`) — even orbit-position ⟺ square — via Euler's criterion
and `g^j ≡ 1 ⟺ ord g ∣ j` (`pow_one_iff_ord_dvd`, the `ord_dvd` of this chapter
plus its converse `pow_dvd_one`).  Because the powers `g⁰,…,g^{p−2}` exhaust the
units (`tau_mem_perms` ⇒ `dlog_exists`), every unit has a discrete log, giving
`qr_iff_even_dlog`: `∃ k, a = g^k % p ∧ (QR(a) ⟺ 2 ∣ k)`.  Narrative:
`theory/essays/synthesis/the_quadratic_character_is_a_discrete_log_parity.md`.

## Open frontier

None for cyclicity, the classical Zolotarev route, or the discrete-log parity
(all closed, all odd primes).  The `(ℤ/p)*`-cyclic infrastructure (order
arithmetic, primitive roots) is reusable for any later character-sum direction.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.NumberTheory.ModArith
python3 ../tools/scan_axioms.py E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot   # 9 PURE / 0 DIRTY
python3 ../tools/scan_axioms.py E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle  # 47 PURE / 0 DIRTY
```
