# Frontier — Lagrange's four-square theorem (`∀ n, ∃ a b c d, n = a²+b²+c²+d²`)

**Date**: 2026-06-04.  **Status**: CLOSED (∅-axiom).  `NumberTheory.FourSquare.nat_isSum4 :
∀ n, isSum4 ↑n` is axiom-free (`#print axioms → does not depend on any axioms`); 35 PURE / 0
dirty.  **Tier**: 1 (promotion to `theory/` per `PROMOTION_CRITERIA` is the follow-on).

## Closing assembly (∅-axiom)

The Euler-descent route closed end to end (over `ℤ`, no quaternion gcd):
  - `seed_multiple` — `four_square_seed` ⟹ `k·p = x²+y²+1²+0²`, `1 ≤ k < p` (`k·p ≤ 2m²+1 < p²`).
  - `dvd_dec` / `searchDiv` / `exists_prime_factor` — constructive least-divisor prime
    factorization (`n ≥ 2 ⟹ ∃ prime q ∣ n`), ∅-axiom via the `n % k` bridge (no `Decidable`
    propext; `Nat.dvd_refl` / `Nat.succ_ne_zero` both leak propext — replaced by `⟨1, (mul_one
    _).symm⟩` and `Nat.noConfusion`).
  - `prime_isSum4` — `p = 2 = 1²+1²+0²+0²` directly; odd `p` via `seed_multiple` + `descent_rec`.
  - `nat_isSum4` — all `n` via prime factorization + `isSum4_mul` (`n = 0,1` base cases).

## Pillar II — Euler descent (CLOSED, ∅-axiom; avoids the quaternion gcd)

Stays over `ℤ` with ring identities + `centered_div_int`.  `NumberTheory.FourSquare`:
  - **`four_sq_id` (DONE)** — Euler's four-square identity (ring_intZ); `isSum4_mul`.
  - **`descent_core` (DONE)** — `m·p = Σaᵢ²`, `aᵢ = qᵢm+Aᵢ`, `m·r = ΣAᵢ²` ⟹ `p·r = Σdⱼ²`
    (Euler ⟹ `(mp)(mr) = Σcⱼ²`, each `m∣cⱼ`, `/m²`).  + pure ℤ cancellation
    (`mul_left_cancel_pos`, `eq_zero_of_mul_pos`, `le_of_not_lt`, `lt_of_mul_lt_mul_pos`,
    `sq_eq_zero`).
  - **even-`m` branch (DONE)** — `int_even_or_odd`, `sum_two_sq_of_even_diff`, `two_c_ne_one`,
    `sq_sum_even_imp_diff_even`, `combine`, `halve4` (8-case parity pigeonhole), and
    ★`halve_step : isSum4 (2m'·p) ⟹ isSum4 (m'·p)`.
  - **odd-`m` strict bound (DONE)** — `Asq_bound` (`2|A|≤2k+1 ⟹ 4A² ≤ (2k)²`, the odd
    refinement that kills the `r=m` edge), `sq_nonneg`, `add_le_add`, and ★`rlt`
    (`4Aᵢ²≤(m−1)², ΣAᵢ²=m·r ⟹ r<m`).  `odd_descent` itself is ~2/3 validated in scratch
    (centred residues → explicit `r` → `descent_core` → `rlt`/`0≤r` all check); remaining
    inside it: pure `natAbs` casts (`↑r.natAbs = r` for `r≥0`, `0<r` from `0≤r ∧ r≠0`,
    `1≤r.natAbs`), the `r=0`→`m∣p` exclusion (approach validated: `ΣAᵢ²=0 ⟹ Aᵢ=0 ⟹ m∣p`
    via `mul_left_cancel_pos` + `int_dvd_to_nat`), and the ℤ→ℕ conversion of `r`.

### Then (glue)
  - `nat_even_or_odd` + a fuel recursion (`m≤fuel`, `1≤m<p`): odd ⟹ `odd_descent`, even ⟹
    `halve_step`, both shrink `m`; `m=1 ⟹ isSum4 p`.
  - seed→initial-multiple (`four_square_seed` ⟹ `k·p = x²+y²+1²+0²`, `k<p`) ⟹ `isSum4 p`.
  - all `n`: `2 = 1²+1²+0²+0²`; primes by the above; composites by `isSum4_mul`.

### Remaining (precise)
  1. **Residue setup** — `centered_div_int_sq aᵢ m` ⟹ `aᵢ = qᵢm + Aᵢ`, `4Aᵢ² ≤ m²`.  `r` is
     **explicit**: `r = p − 2Σaᵢqᵢ + mΣqᵢ²`, `m·r = ΣAᵢ²` by `ring_intZ`.  `ΣAᵢ² ≤ m²` ⟹
     `0 ≤ r ≤ m` (needs positive-mul `≤`-cancel lemmas).
  2. **`r ≥ 1`** (`r=0` excl.) — `Aᵢ=0 ⟹ m∣aᵢ ⟹ m²∣mp ⟹ m∣p`; `m<p` prime ⟹ `m=1`, contra.
  3. **`r < m`** — ★ **cleaner route found** (avoids the `r=m` mod-8 crux): split the recursion
     by parity of `m`.
       - **`m` odd** (`≥ 3`): centred residues satisfy `2|Aᵢ| ≤ m` with `2|Aᵢ|` even `≤` odd `m`
         ⟹ `2|Aᵢ| ≤ m−1` ⟹ `4Aᵢ² ≤ (m−1)²` ⟹ `ΣAᵢ² ≤ (m−1)² < m²` ⟹ `r < m` **strictly,
         no `r=m` edge**.
       - **`m` even**: parity-halve instead of centred descent — `mp = Σaᵢ²` even ⟹ even count
         of odd `aᵢ`; pair the four into two same-parity pairs `(a,b),(c,d)`; then
         `((a+b)/2)²+((a−b)/2)²+((c+d)/2)²+((c−d)/2)² = (a²+b²+c²+d²)/2 = (m/2)·p` — a ring
         identity on the halved integers.  `m → m/2 < m`.  (Pairing = parity casework, not mod-8.)
  4. **Fuel recursion** on `m` (`1 ≤ m < p`): odd ⟹ centred-strict, even ⟹ halve, both shrink
     `m`; reach `m=1` ⟹ `p = Σ4²`.
  5. **Seed → initial multiple** — `four_square_seed` ⟹ `k·p = x²+y²+1²+0²`, `1 ≤ k < p`.
  6. **All `n`** — `2=1²+1²+0²+0²`; primes above; composites by `isSum4_mul`.

----

**Date**: 2026-06-04.  **Status**: Pillar I CLOSED (∅-axiom); Pillar II open.  **Tier**: 1.

## Pillar I — DONE (∅-axiom, constructive)

`NumberTheory.FourSquareSeed.four_square_seed` (axiom-free): for an odd prime `p = 2m+1`,
`∃ x y, x ≤ m ∧ y ≤ m ∧ p ∣ (x²+y²+1)`.  The repo's **first additive pigeonhole** (vs the
multiplicative Lagrange-root bound), and **constructive** — a bounded 2-D search `findXY` whose
`none`-branch is refuted by `no_inj_lt` on the map `gval` (`x²%p` / `p−1−y²%p`), so the witness
is produced, not merely shown non-absent (no `Classical`).  16 PURE theorems incl. `sq_distinct`
(squares injective on `[0,m]` mod `p`, ℕ-only, dodging the propext-dirty `Int.natAbs` triangle),
`nat_prime_dvd_mul` (ℕ prime-Euclid via `a%p`, dodging the propext-dirty `Decidable (p∣a)`),
`gval_inj_or_seed`.

----

(original scoping below)

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
