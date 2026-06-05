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
- `Sa_eq` (PURE): `Σ↑(a·x) = ↑a·Σ↑x`.
- `residue_fold_even` (PURE): the Eisenstein crux `2 ∣ (Sr − Sfold − ↑p·Imu)` (per-element `2·(…)`).
- `floor_mu_even` (PURE): for odd unit `a` and odd prime `p`, `2 ∣ (Sfloor + Imu)` — the floor sum
  ≡ μ (mod 2) in indicator form.  (`two_prime` rewritten pure: avoids `decide`-on-`∣`, which
  pulls `propext` via `decidable_of_iff`.)
- `imu_eq_countNeg` (PURE): `Imu = ↑(countNeg ((seg m).map (sgFn a p m)))` — the μ-indicator sum is
  the μ-count.  (Un-privated `sgFn_lo`/`sgFn_hi` in `GaussLemma`.)
- ★ **`floor_qr` (PURE) — STEP 1 COMPLETE.**  `(∃z, z²≡a) ↔ (2:Int) ∣ Σₓ∈[1,m] ↑⌊a·x/p⌋`, for an
  **odd unit `1 ≤ a < p`** and odd prime `p`.  I.e. `a` is a QR mod `p` ⟺ the floor sum is even.
  Composes `gauss_mu` + `imu_eq_countNeg` + `floor_mu_even` via `Iff.trans` (NOT `rw`-on-iff —
  that leaks propext) and the `2∣·ℤ ↔ ·%2=0` casts.  This is Eisenstein's lemma in divisibility
  form.
- `floor_bound` (PURE) — step-3 prereq: `p=2m+1, q=2n+1, x≤m ⟹ ⌊q·x/p⌋ ≤ n` (via
  `(2m+1)(n+1) = (2n+1)·m + (m+n+1)`, `ring_nat` + `div_lt_of_lt_mul`).

## ⚠ Step-4 assembly constraint (`a < p`) — IMPORTANT design note

`floor_qr`/`gauss_mu`/`gauss_qr` all require **`a < p`** (`halt`).  Reciprocity applies the
Eisenstein lemma at **`a = q`**, the *other* prime, which may exceed `p`.  Two routes:

1. **Generalize the Gauss stack to coprimality** (`1 ≤ a ∧ p ∤ a`) instead of `a < p`.  `sgFn`
   depends only on `(a·x)%p` (= `a mod p`), and `fold_perm` needs only that `a` is a unit (`p ∤ a`);
   the residue side `z²≡a` becomes `z² ≡ a (mod p)`.  Invasive (touches `gauss_core`, `fold_*`).
2. **Reduce `q ↦ q%p` with a correction term.**  `⌊q·x/p⌋ = (q/p)·x + ⌊(q%p)·x/p⌋` (from
   `q = p·(q/p) + q%p`), so `Σ⌊q·x/p⌋ = (q/p)·Σx + Σ⌊(q%p)·x/p⌋`.  `floor_qr` at `a = q%p` gives the
   parity of `Σ⌊(q%p)x/p⌋`; the rectangle count (step 3) uses the **actual** `Σ⌊qx/p⌋`.  Need the
   parity of the correction `(q/p)·Σx` (`Σx = m(m+1)/2`).  Less invasive but adds bookkeeping.

Recommended: **route 1** (generalize to `p ∤ a`) — cleaner final statement, and the rectangle
count then directly uses `floor_qr`-generalized at `a = q`.

## (DONE) Step 1 — the exact mod-2 chain

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

### Foundations IN PLACE (committed)
- `AddMod213.le_div_iff_mul_le {p} (hp : 0<p) (y a) : y ≤ a/p ↔ y*p ≤ a` (PURE) — the
  divisor-side of the per-column count.  (Lean-core `Nat.le_div_iff_mul_le` and `Nat.div_add_mod`
  both pull propext; this is the pure replacement, in `AddMod213` to dodge the NatDiv213 cycle.)
- `floor_bound (m n x) (x≤m) : (2n+1)·x/(2m+1) ≤ n` (PURE, in QuadraticReciprocity).
- `sumZ_append`, `map_append'` (`…Linalg213.Laplace`), `seg`/`mem_seg`/`seg_length` (`GaussLemma`).
  `iota (n+1) = iota n ++ [n]` is **definitional** (`from rfl`), so `seg (n+1) = seg n ++ [n+1]`.

### Step 3 — CLOSED (committed)
`floor_sum_rectangle` (PURE): for `p=2m+1, q=2n+1`, `p∤q·x` (`x∈[1,m]`), `q∤p·y` (`y∈[1,n]`),
`Σ_{x∈[1,m]} ⌊q·x/p⌋ + Σ_{y∈[1,n]} ⌊p·y/q⌋ = m·n` (over ℤ).  **This is the analytic heart of
reciprocity** (Eisenstein form).  Built from the full step-3 sequence below, all PURE:
`seg_succ`, `count_all`, `count_le_eq`, `elem_col`, `colCount_eq_floor`, `elem_tri`, plus generic
`Linalg213/SumLinear.{sumZ_map_zero, sumZ_swap}` (finite Fubini) and
`AddMod213.le_div_iff_mul_le`.

### Step 4 — the QR-symbol form needs the Gauss-stack generalization
The symbol statement `(p/q)·(q/p) = (−1)^(m·n)` reads, via `floor_qr`,
`(QR_p(q) ⟺ Σ⌊qx/p⌋ even)` and `(QR_q(p) ⟺ Σ⌊py/q⌋ even)`; with `floor_sum_rectangle`
(`Σ⌊qx/p⌋ + Σ⌊py/q⌋ = mn`) the two parities sum to `mn`'s parity — immediate.  **But both uses of
`floor_qr` need residue = the OTHER prime** (`q` mod `p`, `p` mod `q`), each requiring `a < modulus`
— `q < p` AND `p < q` is impossible.  So the symbol form is **blocked** on generalizing the Gauss
stack from `a < p` to `1 ≤ a ∧ p ∤ a` (residue side `z² ≡ a (mod p)` instead of `z²%p = a`):
`fold_perm` (needs only `p ∤ a`, currently `a<p`) → `gauss_core` → `gauss_qr` → `gauss_mu` →
`floor_mu_even`/`floor_qr`.  `floor_sum_rectangle` itself is **independent** of this — it's done.
Once `floor_qr` is generalized, `quadratic_reciprocity` is a short parity assembly.

**Precise generalization recipe (verified by inspection of GaussLemma):**
- In `GaussLemma`, `halt : a < p` is used **only** via `not_dvd_unit p a ha1 halt : ¬ p ∣ a`
  (lines 160, 225).  So replace the hypothesis `halt : a < p` with `hnpa : ¬ p ∣ a` throughout
  `fold_mem`, `fold_inj`, `fold_perm`, `gauss_core`, `gauss_qr` — the bodies just drop the
  `not_dvd_unit` call and use `hnpa` directly.  (`res_cancel` needs `x < p`, about `x∈[1,m]`, not
  `a` — unaffected: `m < p` via `m_lt_p`.)
- **Residue side must change** `z² % p = a` → `z² % p = a % p` (i.e. `z² ≡ a (mod p)`), since for
  `a ≥ p` the old form is vacuously false.  This also touches Euler `qr_iff_pow_one`
  (`EulerCriterion`/`EulerConverse`) — the Euler criterion itself holds for `a` coprime to `p`
  with the `≡` residue side; re-thread `1 ≤ a < p` → `1 ≤ a ∧ ¬p∣a` + `z²≡a` there too.
- Then `gauss_mu`, `floor_mu_even`, `floor_qr` re-thread mechanically (they already only pass `halt`
  down).  `floor_qr` generalized: `(∃z, 1≤z ∧ z<p ∧ z²%p = a%p) ↔ 2 ∣ Σ⌊a·x/p⌋` for `1≤a`, `p∤a`,
  `a` odd, `p` odd prime.
- **Assembly** `quadratic_reciprocity`: apply generalized `floor_qr` at `(p, q)` and `(q, p)`
  (residues `q`, `p` — coprime since `p≠q` primes), combine the two parities with
  `floor_sum_rectangle` (`Σ⌊qx/p⌋ + Σ⌊py/q⌋ = mn`) ⟹ `(QR_p(q) ⟺ QR_q(p)) ⟺ mn even`.  Discharge
  the `floor_sum_rectangle` side-conditions `p∤q·x`, `q∤p·y` from primality (`p∤q`, `p∤x` for
  `x∈[1,m]` since `x<p`).

### (historical) Step-3 lemma sequence (build-ready, over `ℤ` reusing `sumZ`)
Work with **Int indicators** `(if P then (1:Int) else 0)` so `sumZ`/`sumZ_map_add` give the Fubini
swap for free (avoids a separate Nat list-sum + `Nat.min` whose lemmas `min_eq_right`/`min_zero`
pull propext).
1. `seg_succ (n) : seg (n+1) = seg n ++ [n+1]` — `rw [seg, seg, show iota (n+1)=iota n++[n] from rfl,
   map_append']`.
2. `count_all (n) : sumZ ((seg n).map (fun _ => (1:Int))) = ↑n` — induction + `seg_succ` +
   `sumZ_append`.  (Watch `sumZ [1] = 1+0` defeq; finish with an explicit `Int` `add_zero`/`show`.)
3. `count_le_eq (K n) (h : K ≤ n) : sumZ ((seg n).map (fun y => if y ≤ K then (1:Int) else 0)) = ↑K`
   — induction on `n`; at `n+1`, split `K ≤ n+1` into `K ≤ n` (IH; the new term `if n+1≤K` is `0`)
   vs `K = n+1` (all of `seg n` satisfy `y ≤ n < K` → `map_congr` to `count_all n = ↑n`, new term
   `1`).  **Avoids `Nat.min`** (whose lemmas are propext-dirty).
4. `colCount_eq_floor (p q x n) (hp : 0<p) (hndvd : ¬ p ∣ q*x) (hbnd : q*x/p ≤ n) :
   sumZ ((seg n).map (fun y => if p*y < q*x then (1:Int) else 0)) = ↑(q*x/p)` — rewrite the predicate
   `p*y < q*x ⟺ y ≤ q*x/p` (via `le_div_iff_mul_le` + `mul_comm`; the `<`-vs-`≤` gap is closed by
   `hndvd`: `p*y = q*x ⟹ p ∣ q*x`), then `count_le_eq` with `hbnd`.
5. `floor_sum_rectangle (m n) (hp prime, hq prime, p∤q) : Σ_{x∈seg m} ⌊q·x/p⌋ + Σ_{y∈seg n} ⌊p·y/q⌋
   = m·n` (`p=2m+1, q=2n+1`).  Both Σ as Int via `colCount_eq_floor`; the cross term equals one
   nested `sumZ` two ways (Fubini = `sumZ_map_add` induction), and `[qx>py]+[qx<py]=1` (trichotomy,
   no `=` by `p∤qx`) collapses the grid to `count_all`²-style `m·n`.  The one genuinely new lemma.

### Step 4 — STILL BLOCKED on the `a < p` constraint (see §"Step-4 assembly constraint" above)
`floor_qr` needs `a < p`; reciprocity wants `a = q`.  **Resolve first** (recommended: generalize the
Gauss stack `gauss_core`/`gauss_qr`/`gauss_mu`/`floor_qr` from `a < p` to `1 ≤ a ∧ p ∤ a`).  Until
then step 3's `floor_sum_rectangle` is provable but does not yet assemble into
`quadratic_reciprocity`.

### Misc
- A `legendre` symbol def (Int-valued `±1`) would let the final statement read `(p/q)*(q/p) = ±1`
  cleanly — optional sugar over `floor_qr`.

Estimated: still a multi-session build.  Watch the usual propext-dirty core (`Nat.*` div/sub/mod —
use `NatDiv213`/`AddMod213`/`NatHelper` pure replacements; verify each private helper with
`#print axioms` since the scanner skips privates).

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/{GaussLemma,SecondSupplement,LegendreMultiplicative,
EulerFirstSupplement}.lean`; `…/GaussLemma.lean` `fold_perm` (the permutation for step 1);
`Meta/Nat/NatDiv213.lean` (pure div).
