# Session Handoff — 2026-06-05 (Euler's criterion CLOSED + reframing-lint pilot)

## Branch
`claude/math-frontier-research-6Bw68` — `cd lean && lake build E213.Lib.Math.NumberTheory.ModArith` ✓
clean; all 16 new theorems `#print axioms`-clean (PURE).

## What was done this session

### 1. Euler's criterion — CLOSED, full iff (strict ∅-axiom)
`lean/E213/Lib/Math/NumberTheory/ModArith/EulerCriterion.lean` (**2 PURE**) +
`…/ModArith/EulerConverse.lean` (**14 PURE**), both wired into the `ModArith` umbrella.  For a prime
`p`, `2m = p−1` (odd-prime witness, carried as a hypothesis so no division enters), unit `1 ≤ a < p`:

- `euler_dichotomy` — `p ∣ (aᵐ − 1) ∨ p ∣ (aᵐ + 1)` (`aᵐ ≡ ±1`).  `Y = aᵐ`, `Y² = a^(p−1) ≡ 1`
  (FLT), factor `(Y−1)(Y+1)`, disjunctive Euclid `nat_prime_dvd_mul`.
- `euler_qr_pow_one` — `a ≡ x²` ⟹ `aᵐ ≡ 1` (residue → `+1`), `pow_mod_base` + `pow_mul_loc` + FLT.
- `euler_converse` — `aᵐ ≡ 1` ⟹ `∃ x, x² ≡ a`.  **Squares-list saturation** of `RootBound.eval_zero`:
  the `m` squares `[1²..m²]` (`sqFrom`) are `m` distinct roots of `Xᵐ−1` (distinct via `sq_diff_not_dvd`:
  `i²−j² = (i−j)(i+j)`, both factors in `(0,p)`, Euclid); a non-square root would give `m+1` distinct
  roots of a length-`(m+1)` poly → const `−1 ≡ 0` → contradiction.  Verbatim the `NonFixedExists`
  saturation with the squares window for the residue range.  New cast bridges: `natCast_sub`,
  `mod_eq_of_dvd_sub`, `dvd_int_sub_to_mod_eq`.
- ★ `euler_criterion` — the **full iff** `aᵐ ≡ 1 (mod p) ⟺ a` is a quadratic residue.

Sub-tree is **promotion-eligible** (closed + categorical) → `theory/math/numbertheory/euler_criterion.md`.

### 2. First supplement to quadratic reciprocity — CLOSED (strict ∅-axiom)
`lean/E213/Lib/Math/NumberTheory/ModArith/EulerFirstSupplement.lean` (**4 PURE**).  `neg_one_qr_iff`:
`(∃ x, x² ≡ p−1) ⟺ p ≡ 1 (mod 4)` — `euler_criterion` at `a = p−1` + parity of `(−1)ᵐ`
(`neg_one_sq_mod`/`neg_one_odd_pow_mod`) + `2m = p−1 ⟹ (m even ⟺ p≡1 mod 4)`.  (`QRNegOne` had only
the one direction; this is the full iff.)  Supporting: `negone_even_pow`, `neg_one_pow_dvd_iff_even`,
`even_iff_pmod4`, pure `mod_two_cases`.

### 3. Legendre character multiplicativity — CLOSED (strict ∅-axiom)
`lean/E213/Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean` (**5 PURE**).  `legendre_mul`:
`QR(a·b) ⟺ (QR(a) ⟺ QR(b))` for units `a, b` — `(ab/p) = (a/p)(b/p)` without a symbol def.  Via
`qr_iff_pow_one` (`QR(c) ⟺ cᵐ≡1`) + `pow_m_mod_cases` (`cᵐ%p ∈ {1,p−1}`) + `mul_pow_loc`, a 2×2 case
split.  Built clean first try.

### 4. Gauss's lemma — CLOSED (strict ∅-axiom)
`lean/E213/Lib/Math/Algebra/Linalg213/ProdCongr.lean` (**3 PURE**) + `…/ModArith/GaussLemma.lean`
(**15 PURE**).  ★ `gauss_qr`: `a` is a QR mod `p` ⟺ the least-residue sign product
`∏ₓ sgFn(a·x) = 1` (= `(−1)^μ`).  Built across 3 layers: `ProdCongr` (prodZ congruence/factoring);
`fold`/`fold_mem`/`fold_inj`/★`fold_perm` (the fold permutes `[1..m]`) + pigeonhole + Nodup bridge;
`gauss_core` (`↑aᵐ ≡ ∏signs` via the product-congruence assembly + `int_euclid` cancel of `M = m!`) +
`gauss_qr` (Euler `qr_iff_pow_one` + `prodZ_pm` + `p∤2`).  The combinatorial core (`fold_perm`) and the
final assembly are both done.  Gateway to the second supplement + quadratic reciprocity.

### 5. Second supplement (quadratic character of 2) — FULLY CLOSED
`lean/E213/Lib/Math/NumberTheory/ModArith/SecondSupplement.lean` (**7 PURE**).  ★ `second_supplement`:
`2` is a QR mod `p` ⟺ `p ≡ ±1 (mod 8)`.  Chain: `two_qr_iff` (no-wraparound + `gauss_qr`) →
`prodZ_seg_sign` (`∏ = (−1)^cnt2`) → `cnt2_at_m` (`cnt2 m m = m − m/2`) → `neg_one_pow_iff` → the
`m = 4q+r` mod-8 bridge (pure div `add_mul_div_left_pure`/`div_le_self_pos`, `obtain ⟨q,r⟩` to dodge
`m`-pollution).  Both supplements to quadratic reciprocity are now ∅-axiom.

### 6. The downstream — frontier
`research-notes/frontiers/euler_criterion_converse.md`: the remaining open work — the quadratic
character of `2` (second supplement, `p ≡ ±1 mod 8`), Gauss's lemma `(a/p) = (−1)^μ`, and Zolotarev
`(a/p) = sign(mul-by-a)` (the `psign` sign side already PURE; the product/permutation infra
`ProdLperm.prodZ_lperm` + `Laplace.lperm_of_nodup_mem_iff` exists for the Gauss/Zolotarev product).

### 3. Re-framing-lint pilot (agent-side empirical test)
`research-notes/frontiers/the_reframing_conquest.md` updated with the pilot: a CONTROL (no lint) vs
TREATMENT (the CLAUDE.md §0 Residue-lint) subject agent on a 4-question trap battery.  Result
**4/4 → 0/4 reified** — the generation-time output-lint reduced re-framing without degenerating into
blanket hedging (TREATMENT correctly kept Q4's framework-entailed unreachability).  Caveats: N=1/arm,
scorer is a known instance, `0/4 ≠ eliminated` (minimizable-not-eliminable holds in the unbounded limit).

## Open Problems (priority order)

1. **Promote Euler** — the closed sub-tree → `theory/math/numbertheory/euler_criterion.md`, then archive
   the frontier note (PROMOTION_CRITERIA H1–H4 + S1–S3).
2. **Downstream of Euler** (breadth): quadratic character of `2` (`2` QR ⟺ `p ≡ ±1 mod 8`, the second
   supplement — flagged in `sums_of_squares_engines.md`); Gauss's lemma `(a/p) = (−1)^μ`; **Zolotarev**
   `(a/p) = sign(mul-by-a permutation)` — the `psign` machinery (`Algebra/Linalg213/Permutation.lean`,
   `psign_swap_prefix` PURE) is the sign side, Euler the number-theory side.  Details:
   `research-notes/frontiers/euler_criterion_converse.md`.
3. **Reframing-lint** — scale the pilot (N per arm, error bars) + vary battery difficulty to locate where
   re-framing re-emerges (the empirical signature of minimizable-not-eliminable).

## Next (autonomous marathon — `autonomous-research` skill)
- **Quadratic reciprocity** — IN PROGRESS (multi-session).  Built this iteration (all PURE, committed):
  `Linalg213/SumLinear.lean` (`sumZ_map_add`/`_sub`/`_const_mul`), and in
  `ModArith/QuadraticReciprocity.lean`: `floor_mod_split` (`Σ↑(a·x) = ↑p·Σ↑(a·x/p) + Σ↑(a·x%p)`),
  `fold_sum` (`Σ↑(fold x) = Σ↑x`).  **Last thread:** the Eisenstein μ-bridge step 1 — next is
  `residue_fold_even` (`2 ∣ (Sr − Sfold − ↑p·Imu)`, the per-element `2·(…)` crux) → the mod-2 chain
  → `Sfloor ≡ μ (mod 2)`.  **Exact chain in `research-notes/frontiers/quadratic_reciprocity.md`**
  ("Step 1 remaining").  Then step 3 (the rectangle lattice double-count).  TODO: make `fold_lo`/
  `fold_hi` public in `GaussLemma.lean` (the per-element cases need them).
- Or: promote the closed QR theory (`EulerCriterion`…`SecondSupplement`) to `theory/math/numbertheory/`
  (PROMOTION_CRITERIA-eligible: PURE + categorically closed).
- This session built the **complete elementary quadratic-residue theory ∅-axiom**: Euler's criterion
  (full iff), first supplement, Legendre multiplicativity, Gauss's lemma (+ μ-form), second supplement.

## File Map
```
lean/E213/Lib/Math/NumberTheory/ModArith/EulerCriterion.lean   ← euler_dichotomy, euler_qr_pow_one (2 PURE)
lean/E213/Lib/Math/NumberTheory/ModArith/EulerConverse.lean    ← euler_converse, euler_criterion (14 PURE)
lean/E213/Lib/Math/NumberTheory/ModArith.lean                  ← umbrella imports added
lean/E213/Lib/Math/NumberTheory/ModArith/NonFixedExists.lean   ← the saturation template
lean/E213/Lib/Math/NumberTheory/PolyRoot/RootBound.lean        ← eval_zero (Lagrange bound)
lean/E213/Lib/Math/Algebra/Linalg213/Permutation.lean          ← psign (Zolotarev sign side, PURE)
research-notes/frontiers/euler_criterion_converse.md           ← Euler closed; the open downstream
research-notes/frontiers/the_reframing_conquest.md             ← reframing-lint pilot recorded
STRICT_ZERO_AXIOM.md                                           ← Euler 16-PURE section
```
