# Lifting the Exponent — `v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)`

The lifting-the-exponent lemma (LTE) computes the exact `p`-adic valuation of `aⁿ − bⁿ`.
For an odd prime `p` dividing `a − b` but not `b`, the valuation *lifts* by exactly the
valuation of the exponent:

```
v_p(aⁿ − bⁿ) = v_p(a − b) + v_p(n).
```

The whole theorem is strict ∅-axiom, assembled bottom-up from a two-variable binomial
theorem and an ultrametric valuation law — no Mathlib, no `Classical`, no `sorry`.

## 213-native answer

There is **no `p`-adic valuation primitive**.  `v_p(n)` is the count-Lens reading of the
prime-power axis at `p`: `vp p n` is the largest `k` with `pᵏ ∣ n` (`seed/AXIOM/06_lens_readings.md`
§6.7), characterized internally by `le_vp_iff : pᵏ ∣ n ↔ k ≤ vp p n`.  LTE is then a
statement about how this count behaves under the difference-of-powers operation.

The proof is **counting, not analysis** (per the repo's algebraic-priority principle).  Two
facts drive it:

1. **Ultrametric strict minimum** — if `v_p(x) < v_p(y)` then `v_p(x+y) = v_p(x)`
   (`vp_add_eq_min`): a sum is pinned to its uniquely-least-valued term.  The `pᵏ` dividing
   the small term divides the sum; the next power divides the large term but not the small,
   so it cannot divide the sum.
2. **The binomial decomposition** — writing `a = b + d` (`d = a − b`), the two-variable
   binomial theorem gives `(b+d)ⁿ − bⁿ = n·b^{n−1}·d + R` with `R = Σ_{k≥2} C(n,k) b^{n−k} dᵏ`.
   The middle term carries `v_p = v_p(d) + v_p(n)`; the tail `R` carries strictly more.

The oddness of `p` (`3 ≤ p`) enters at exactly one place: in the prime-exponent case the
`k = p` tail term is `dᵖ`, whose valuation `p·v_p(d)` must exceed `v_p(d)+1` — true iff
`(p−1)·v_p(d) ≥ 2`, which needs `p ≥ 3`.  (For `p = 2` the lemma genuinely fails; the `+1`
becomes `v_2(a+b)`.)

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/NumberTheory/` (the `LiftingExponent*` + `BinomialTwoVar`
  + `PowSubPowFactor` files)
- **∅-axiom status**: **43 PURE / 0 DIRTY**

| file | content | PURE |
|---|---|---|
| `PowSubPowFactor.lean` | explicit homogeneous factorization `aⁿ⁺¹−bⁿ⁺¹ = (a−b)·Σaⁱbⁿ⁻ⁱ` (ℤ) | 6 |
| `LiftingExponent.lean` | cofactor congruence `(a−b) ∣ (Σaⁱbⁿ⁻ⁱ − (n+1)bⁿ)`, coprimality (the `p∤exp` algebraic core, ℤ-divisibility form) | 7 |
| `BinomialTwoVar.lean` | two-variable binomial theorem `(b+d)ⁿ = Σ C(n,k) b^{n−k} dᵏ` (ℕ) | 6 |
| `LiftingExponentPP.lean` | ultrametric package: `vp_add_eq_min` (strict-min law), `dvd_sumTo`/`le_vp_sumTo` (tail bound) | 3 |
| `LiftingExponentMain.lean` | prime-power kernel `v_p(aᵖ−bᵖ)=v_p(a−b)+1` (`lifting_prime_power`) | 10 |
| `LiftingExponentCoprime.lean` | coprime-exponent case `v_p(aᵐ−bᵐ)=v_p(a−b)` for `p∤m` (`lifting_coprime`) | 5 |
| `LiftingExponentGeneral.lean` | Step A `vp_pow_pk` + the general theorem `lte` | 6 |

## Proof architecture

```
add_pow  (two-variable binomial theorem)
   │
   ├──► lte_decomp : (b+d)ᵖ − bᵖ = p·b^{p−1}·d + R          (extract k=0, k=1 terms)
   │
vp_add_eq_min  (ultrametric strict-minimum law)
le_vp_sumTo    (Σ-divisibility lower bound)   +  prime_dvd_choose (p ∣ C(p,k))
   │
   ▼
lifting_prime_power : v_p(aᵖ − bᵖ) = v_p(a−b) + 1           [the hard kernel]
lifting_coprime     : v_p(aᵐ − bᵐ) = v_p(a−b)      (p ∤ m)  [middle v_p = v_p(d), no p∣C]
   │
   ▼
vp_pow_pk : v_p(a^{pᵏ} − b^{pᵏ}) = v_p(a−b) + k             [iterate the kernel k times]
   │  +  factor n = pᵏ·m (k = v_p n, p ∤ m)
   ▼
lte : v_p(aⁿ − bⁿ) = v_p(a−b) + v_p(n)
```

The prime-power kernel is the only delicate step: it needs `p ∣ C(p,k)` for `0 < k < p`
(already in `ModArith/LucasTheorem.prime_dvd_choose`) so that each tail term gains a factor
of `p` beyond the `dᵏ` factor, lifting `v_p(R) ≥ v_p(d) + 2` strictly above the middle
term's `v_p(d) + 1`.

## Statement

```lean
theorem lte (a b p n : Nat) (hp : Prime213 p) (hp3 : 3 ≤ p)
    (hba : b < a) (hpd : p ∣ (a - b)) (hpb : ¬ p ∣ b) (hn : 1 ≤ n) :
    vp p (a ^ n - b ^ n) = vp p (a - b) + vp p n
```

## Craft notes (∅-axiom hazards encountered)

- The repo's `binomSum` only proved the `b = 1` form `(a+1)ⁿ = Σ C(n,k) aᵏ`; the homogeneous
  two-variable version was genuinely missing and is the load-bearing new infrastructure.  Its
  truncated exponent `b^{n−k}` is handled by the pure `nat_succ_sub` (`(n+1)−k = (n−k)+1`).
- Core `Nat.sub_pos_of_lt`, `Nat.add_mul`, `Nat.pow_mul`, `Int.ofNat_sub` all leak `propext`;
  pure replacements (`sub_pos_pure`, `PureNat.add_mul`, `PowBasic.pow_mul_pure`, the
  `a = b + p·k` route) keep the chain clean.
- **Well-founded-recursion trap**: inside a theorem proved by `induction k`, calling the
  theorem *recursively* (instead of using `ih`) silently pulls `propext` via the equation
  compiler's well-founded fallback.  Always use `ih`.

## Scope / open edge

`p = 2` is excluded (the lemma changes form: `v_2(aⁿ−bⁿ) = v_2(a−b)+v_2(a+b)+v_2(n)−1` for
even `n`).  The `p = 2` variant is not yet formalized.
