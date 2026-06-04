# Frontier — Lagrange's four-square theorem (`∀ n, ∃ a b c d, n = a²+b²+c²+d²`)

**Date**: 2026-06-04.  **Status**: open marathon (seeded).  **Tier**: 1.

The next genuinely-new target after the disc-`−3`/`−4`/parametric `ℤ[√−D]` representation arc.
Unlike those, four-square needs a *different counting principle* (additive pigeonhole, not the
multiplicative Lagrange-root bound) and a *non-commutative* descent (the Hurwitz quaternion
order).  Both are new to the repo.

## Two pillars

**Pillar I — the seed (additive pigeonhole).**  For an odd prime `p = 2m+1`:
> `∃ x y, p ∣ x² + y² + 1`.

The `(m+1)` values `{x² mod p : 0 ≤ x ≤ m}` are pairwise distinct mod `p`, and so are the
`(m+1)` values `{−1−y² mod p}`; together `2m+2 = p+1 > p` values in `Fin p`, so two coincide —
necessarily one from each family (distinctness rules out within-family), giving
`x² ≡ −1−y²`, i.e. `p ∣ x²+y²+1`.  Tool: `Combinatorics.Pigeonhole.no_inj_lt`
(`N < k → Fin k → Fin N` has a collision).

**Pillar II — the quaternion descent.**  In the Hurwitz order `H` (`Hurwitz213`), `N(α) =`
sum of four (half-)squares is multiplicative (Euler's four-square identity = `normSq_mul`), and
`H` is norm-Euclidean (left/right division).  From `p ∣ x²+y²+1 = N(⟨x,y,1,0⟩)` and a gcd
descent, `p = N(π)` for some `π ∈ H`, then a Lipschitz-integer adjustment gives `p =`
sum of four *integer* squares.  Multiplicativity extends prime → all `n` (and `2 = 1²+1²+0²+0²`).

## Progress / bricks laid

  - **`PolyRoot.IntEuclid.mod_eq_imp_dvd_sub` (DONE, PURE)** — `a%p = b%p ⟹ ↑p ∣ (↑a−↑b)`; the
    modular bridge for square-distinctness.
  - **Reusable already in repo**: `int_euclid` (ℤ prime Euclid), `not_dvd_of_natAbs_lt`,
    `le_of_dvd_pos`, `Pigeonhole.no_inj_lt`, `Hurwitz213` (quaternion ring + `normSq_mul`).

## Honest scope / snags

  - **Pillar I**: `sq_distinct` (`x,x' ≤ m`, `x²≡x'² mod p ⟹ x=x'`) needs a pure bound
    `natAbs(↑x−↑x') < p` — the core triangle `Int.natAbs_add_le` is `propext`-dirty; route via
    `subNatNat_of_le`/`subNatNat_of_lt` (`Int213.Core`) + `Nat.le_total`, or the order form
    `−p < d < p ∧ p∣d ⟹ d = 0` (needs a positive-mul cancel).  Then the `Fin (p+1) → Fin p`
    map (`i ≤ m ↦ x²%p`, else `↦ p−1−y²%p`) + 3-way injectivity (two within-family via
    `sq_distinct`, one cross = the seed) + `no_inj_lt`.  ~200 lines.
  - **Pillar II**: the Hurwitz order is **non-commutative** and uses half-integer coordinates
    (the 16 unit structure); the gcd descent is left/right-ideal, not the commutative
    `gcd_bezout` reused for `ℤ[ω]`/`ℤ[i]`/`ℤ[√−D]`.  A genuinely separate sub-marathon.

## Why it is novel for the repo

The whole disc-`−3/−4/−D` arc runs on **one** engine (multiplicative Lagrange bound +
commutative norm-Euclidean descent).  Four-square breaks both: an **additive** pigeonhole and a
**non-commutative** descent.  Completing it would be the first ∅-axiom result in the repo that
neither the counting-bound nor the commutative-CD machinery reaches.
