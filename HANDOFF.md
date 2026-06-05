# Session Handoff — 2026-06-05 (Quadratic reciprocity — STEP 1 CLOSED: Eisenstein μ-bridge)

## Branch
`claude/math-frontier-research-6Bw68` — `cd lean && lake build E213.Lib.Math.NumberTheory.ModArith` ✓
clean; all QuadraticReciprocity theorems `#print axioms`-clean (8 PURE).

## What was done this session (autonomous marathon — `autonomous-research`)

Continued the Eisenstein lattice-point route to quadratic reciprocity in
`lean/E213/Lib/Math/NumberTheory/ModArith/QuadraticReciprocity.lean`.  **Step 1 (Eisenstein's
lemma, `(a/p) = (−1)^Σ⌊a·x/p⌋` in divisibility form) is now CLOSED, strict ∅-axiom.**

New PURE theorems (committed, in order):

1. **`floor_mu_even`** — for odd unit `a` and odd prime `p`, `2 ∣ (Sfloor + Imu)` over `[1..m]`
   (`Sfloor = Σ↑⌊a·x/p⌋`, `Imu = Σ(if (a·x)%p ≤ m then 0 else 1)`).  Assembles `floor_mod_split`
   + `Sa_eq` + `fold_sum` + `residue_fold_even` + oddness of `a` (`↑a−1 = 2↑(a/2)`) + `int_euclid`
   (`p` odd).  **Fixed propext leak** in helper `two_prime`: `decide`-on-`∣` pulls propext via
   `decidable_of_iff`; rewrote pure (`d∣2 ⟹ d≤2 ⟹ d<3`, `cases_lt_three`, `0∤2` via `0·c=0≠2`).
2. **`imu_eq_countNeg`** — `Imu = ↑(countNeg ((seg m).map (sgFn a p m)))` (the 0/1 indicator sum is
   the μ-count).  List induction (`ind_sum_countNeg`); `decide` on `(±1:Int)=−1` is propext-free
   (same pattern as `prodZ_sign_eq`).  Un-privated `sgFn_lo`/`sgFn_hi` in `GaussLemma`.
3. ★ **`floor_qr` — STEP 1 COMPLETE.**  `(∃z, z²≡a) ↔ (2:Int) ∣ Σₓ∈[1,m] ↑⌊a·x/p⌋` for odd unit
   `1 ≤ a < p`, odd prime `p` — `a` is a QR mod `p` ⟺ the floor sum is even.  Composes `gauss_mu`
   + `imu_eq_countNeg` + `floor_mu_even` via **`Iff.trans`** (NOT `rw`-on-iff → propext) + the
   `2∣·ℤ ↔ ·%2=0` casts.  Helpers `two_mul_mod`, `two_dvd_to_mod` (PURE).
4. **`floor_bound`** — step-3 prereq: `p=2m+1, q=2n+1, x≤m ⟹ ⌊q·x/p⌋ ≤ n` (each column's floor
   count stays in `[1..n]`).  `(2m+1)(n+1) = (2n+1)·m + (m+n+1)` via `ring_nat` + `div_lt_of_lt_mul`.

## ⚠ Step-4 constraint discovered (recorded in frontier note)

`floor_qr`/`gauss_qr` require **`a < p`**, but reciprocity applies Eisenstein at `a = q` (the other
prime, possibly `> p`).  Two routes (frontier note `quadratic_reciprocity.md` §"Step-4 assembly
constraint"): **(1) generalize the Gauss stack to coprimality `p ∤ a`** (recommended — cleaner,
`sgFn`/`fold_perm` only need `a` a unit), or **(2) reduce `q ↦ q%p` with correction
`Σ⌊qx/p⌋ = (q/p)·Σx + Σ⌊(q%p)x/p⌋`**.

## Addendum 2 (same session) — STEP 3 CLOSED (rectangle double-count)

★★ **`floor_sum_rectangle`** (PURE) — the analytic heart of reciprocity:
for `p=2m+1, q=2n+1`, `p∤q·x` (`x∈[1,m]`), `q∤p·y` (`y∈[1,n]`),
`Σ_{x∈[1,m]} ⌊q·x/p⌋ + Σ_{y∈[1,n]} ⌊p·y/q⌋ = m·n` over ℤ.  Lattice-point count of `[1,m]×[1,n]`
either side of the diagonal `q·x=p·y` (none ON it).  Supporting PURE lemmas, all committed:
- `QuadraticReciprocity`: `seg_succ`, `count_all`, `count_le_eq`, `elem_col`, `colCount_eq_floor`
  (`#{y∈[1,n] : p·y<q·x} = ⌊q·x/p⌋`), `elem_tri` (trichotomy `[py<qx]+[qx<py]=1`).
- `Linalg213/SumLinear`: `sumZ_map_zero`, **`sumZ_swap`** (finite Fubini, `Σₓ Σᵧ = Σᵧ Σₓ`).
- `AddMod213.le_div_iff_mul_le`.

**QuadraticReciprocity.lean now 9 PURE public theorems.**  Steps 1 + 3 of the Eisenstein route are
closed.

### Step 4 (the remaining gateway) — generalize the Gauss stack `a<p` → `p∤a`
The symbol form `(p/q)(q/p)=(−1)^(mn)` needs `floor_qr` at residue = the *other* prime, so the
`a<p` constraint must be relaxed.  **Precise recipe in `frontiers/quadratic_reciprocity.md` §"Step 4"**:
`halt:a<p` in `GaussLemma` is used *only* via `not_dvd_unit → ¬p∣a`, so swap `halt` for `hnpa:¬p∣a`
through `fold_mem/fold_inj/fold_perm/gauss_core/gauss_qr`; change residue side `z²%p=a → z²%p=a%p`
(also in Euler `qr_iff_pow_one`); re-thread `gauss_mu/floor_mu_even/floor_qr`; then assemble
`quadratic_reciprocity` (short parity argument with `floor_sum_rectangle`).  `floor_sum_rectangle`
is independent and already done.

## Addendum (later same session) — step-3 foundation

- **`AddMod213.le_div_iff_mul_le`** (PURE, committed `f7402fc35`): `y ≤ a/p ↔ y·p ≤ a` (`0<p`).
  Pure replacement for `Nat.le_div_iff_mul_le` (propext, as is `Nat.div_add_mod`).  Placed in
  `AddMod213` (not `NatDiv213`) to use the pure `div_add_mod` without the `NatDiv213` import cycle.
  This is the divisor side of the Eisenstein per-column count `#{y : p·y < q·x} = ⌊q·x/p⌋`.
- Scoped the rest of **step 3** (the rectangle double-count) into a build-ready lemma sequence —
  `seg_succ → count_all → count_le_eq → colCount_eq_floor → floor_sum_rectangle` — over `ℤ`/`sumZ`
  (Fubini = `sumZ_map_add`; avoids `Nat.min`, whose `min_eq_right`/`min_zero` are propext-dirty).
  Full recipe in `research-notes/frontiers/quadratic_reciprocity.md` §"Step-3 lemma sequence".
- **Step 4 still blocked** on the `a < p` constraint (generalize the Gauss stack to `p ∤ a` first).

## Next (autonomous marathon)

Per `research-notes/frontiers/quadratic_reciprocity.md`:

- **Step 3 — the rectangle double-count** (the one genuinely new combinatorial lemma):
  `Σ_{x=1}^{m} ⌊q·x/p⌋ + Σ_{y=1}^{n} ⌊p·y/q⌋ = m·n` for distinct odd primes `p,q`
  (`m=(p−1)/2, n=(q−1)/2`).  Lattice-point count over `[1..m]×[1..n]`, split by `qx ≷ py` (none ON
  the diagonal: `p ∤ q·x`).  `floor_bound` is already in place.  Needs: a Nat double-sum framework,
  the per-column count `#{y∈[1,n] : py < qx} = ⌊qx/p⌋`, and the no-on-diagonal from primality.
- **Decide the step-4 route** (recommend route 1: generalize `floor_qr` to `p ∤ a`).
- **Step 4 — assemble `quadratic_reciprocity`**: `(q/p)·(p/q) = (−1)^(m·n)`.

Or (Tier-B): promote the closed Euler/Gauss/supplements sub-tree to `theory/math/numbertheory/`
(PROMOTION_CRITERIA-eligible).

## File Map
```
lean/E213/Lib/Math/NumberTheory/ModArith/QuadraticReciprocity.lean  ← 8 PURE (floor_mod_split,
    fold_sum, residue_fold_even, Sa_eq, floor_mu_even, imu_eq_countNeg, floor_qr, floor_bound)
lean/E213/Lib/Math/NumberTheory/ModArith/GaussLemma.lean            ← sgFn_lo/sgFn_hi now public
lean/E213/Lib/Math/NumberTheory/ModArith/SecondSupplement.lean      ← gauss_mu, countNeg (μ engine)
lean/E213/Lib/Math/Algebra/Linalg213/SumLinear.lean                 ← sumZ linearity (mapped form)
research-notes/frontiers/quadratic_reciprocity.md                   ← STEP 1 done; steps 3–4 plan
STRICT_ZERO_AXIOM.md                                               ← QR section
```
