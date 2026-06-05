# Quadratic reciprocity — frontier (the engine is built)

**Status (2026-06-05).**  All the elementary prerequisites are closed strict ∅-axiom:

- Euler's criterion (`EulerCriterion`, `EulerConverse`): `QR(a) ⟺ aᵐ ≡ 1`.
- First supplement (`EulerFirstSupplement.neg_one_qr_iff`): `−1` QR ⟺ `p ≡ 1 mod 4`.
- Legendre multiplicativity (`LegendreMultiplicative.legendre_mul`): `(ab/p) = (a/p)(b/p)`.
- **Gauss's lemma** (`GaussLemma.gauss_qr`, `gauss_core`) + **μ-form** (`SecondSupplement.gauss_mu`):
  `QR(a) ⟺ μ even`, `μ = #{x ∈ [1,m] : (a·x) mod p > m}` (`= countNeg ((seg m).map (sgFn a p m))`).
- Second supplement (`SecondSupplement.second_supplement`): `2` QR ⟺ `p ≡ ±1 mod 8`.

`gauss_mu` is the engine.  The remaining work is the **Eisenstein lattice-point count**.

## Progress (committed, `ModArith/QuadraticReciprocity.lean` + `Linalg213/SumLinear.lean`)

- `SumLinear` (3 PURE): `sumZ_map_add`, `sumZ_map_sub`, `sumZ_map_const_mul` (additive analog of
  `ProdCongr`).
- `floor_mod_split` (1 PURE): `Σₓ ↑(a·x) = ↑p·Σₓ↑(a·x/p) + Σₓ↑(a·x mod p)` over `[1..m]`.
- `fold_sum` (2 PURE): `Σₓ ↑(fold a p m x) = Σₓ ↑x` (fold_perm + sumZ_lperm).

## Step 1 remaining — the exact mod-2 chain (next pickup)

Abbreviations (`sumZ` over `(seg m).map (·)`): `Sa = Σ↑(a·x)`, `Sfloor = Σ↑(a·x/p)`, `Sr = Σ↑(a·x%p)`,
`Sfold = Σ↑(fold x)`, `Sseg = Σ↑x`, `Imu = Σ (if (a·x)%p ≤ m then 0 else 1)` (the μ-indicator sum).

1. `Sa = ↑a · Sseg`  (`sumZ_map_const_mul` on `↑(a·x) = ↑a·↑x`) — `Sa_eq`.
2. **`residue_fold_even` (the crux):** `2 ∣ (Sr − Sfold − ↑p·Imu)`.  Via `sumZ_map_sub`/`const_mul`,
   reduce to the per-element identity (cases on `(a·x)%p ≤ m`, use `fold_lo`/`fold_hi` — make them
   **public** in GaussLemma): `(↑(a·x%p) − ↑(fold x)) − ↑p·ind = 2·(if … then 0 else ↑(a·x%p) − ↑p)`
   (low → 0; high → `2↑r − ↑p − ↑p = 2(↑r − ↑p)`).  Then `= 2·Σ(…)` so `2 ∣ …`.  Watch `*0` (avoid
   `ring_intZ`; use `mul_zeroZ`/`sub_self_zero`).
3. Combine: `↑a·Sseg = ↑p·Sfloor + Sr` (`floor_mod_split` + step 1) and `Sfold = Sseg` (`fold_sum`) and
   step 2 ⟹ `2 ∣ ((↑a−1)·Sseg − ↑p·(Sfloor − ... ))`; with **`a` odd** (`2 ∣ ↑a−1`) and **`p` odd**
   (`2 ∤ ↑p`, `int_euclid`) ⟹ `2 ∣ (Sfloor + Imu)`, i.e. `Sfloor ≡ Imu (mod 2)`.
4. `Imu = ↑(countNeg ((seg m).map (sgFn a p m)))` (the indicator sum = the μ-count) and
   `Sfloor = ↑(natural floor sum)` ⟹ `(floor sum) ≡ μ (mod 2)`.  With `gauss_mu`: `(a/p) = (−1)^(floor sum)`
   for odd `a` — `legendre_eisenstein`.

## The Eisenstein route to `(p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))`

For an **odd** unit `a` and odd prime `p` (`m = (p−1)/2`):

1. **`μ ≡ Σ_{x=1}^{m} ⌊a·x / p⌋  (mod 2)`** — the Eisenstein refinement of Gauss's μ.  Key step:
   for each `x`, `a·x = p·⌊a·x/p⌋ + (a·x mod p)`; the sign `sgFn` is `−1` iff `(a·x mod p) > m`.
   Summing `a·x` over `x ∈ [1,m]` and reducing mod 2 (with `a` odd, so `a·x ≡ x`, and `Σx`,
   `Σ(a·x mod p)` relate via the fold permutation `fold_perm` which is already PURE) gives
   `μ ≡ Σ⌊a·x/p⌋ (mod 2)`.  This is the main new lemma (`mu_eq_floor_sum`).
2. **The Legendre symbol** `legendre p a := (−1)^μ` (or reuse `gauss_mu`'s `countNeg`); then
   `(a/p) = (−1)^(Σ_{x=1}^{m} ⌊a·x/p⌋)` for odd `a` (`legendre_eisenstein`).
3. **The rectangle double-count** (the heart): for distinct odd primes `p, q`,
   `Σ_{x=1}^{(p−1)/2} ⌊q·x/p⌋  +  Σ_{y=1}^{(q−1)/2} ⌊p·y/q⌋  =  ((p−1)/2)·((q−1)/2)`
   — both sides count lattice points `(x,y)` with `1 ≤ x ≤ (p−1)/2`, `1 ≤ y ≤ (q−1)/2`, below/above
   the diagonal `qx = py` (no lattice point lies ON it since `p ∤ q·x`).  Pure counting over
   `[1..m] × [1..n]` (a nested `seg`/`iota` double sum; the no-on-diagonal uses `p ∤ q·x` from
   primality).  Lemma `floor_sum_rectangle`.
4. **Assemble**: `(q/p)·(p/q) = (−1)^(Σ⌊qx/p⌋ + Σ⌊px/q⌋) = (−1)^(((p−1)/2)((q−1)/2))`
   (`quadratic_reciprocity`).

## New infrastructure needed
- Pure `Nat` floor-division sums: `Σ_{x=1}^{m} f x` over `seg`/`iota` (reuse `sumZ`/list folds);
  `⌊a·x/p⌋ = (a·x)/p` (Nat div, pure — `div_add_mod`).
- `mu_eq_floor_sum` (step 1) — the analytic bridge using `fold_perm` + parity of `Σ`.
- `floor_sum_rectangle` (step 3) — the lattice double-count; the one genuinely new combinatorial lemma.
- A `legendre` symbol def (Int-valued `±1`) tying `gauss_mu`/`gauss_core` together, so the final
  statement reads `(p/q)*(q/p) = ±1` cleanly.

Estimated: a multi-file, multi-session build (comparable to the Gauss-lemma marathon).  Watch the
usual propext-dirty core (`Nat.*` div/sub/mod — use `NatDiv213`/`AddMod213`/`NatHelper` pure
replacements; verify each private helper with `#print axioms` since the scanner skips privates).

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/{GaussLemma,SecondSupplement,LegendreMultiplicative,
EulerFirstSupplement}.lean`; `…/GaussLemma.lean` `fold_perm` (the permutation for step 1);
`Meta/Nat/NatDiv213.lean` (pure div).
