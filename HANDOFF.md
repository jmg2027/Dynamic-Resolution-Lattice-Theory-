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

### 4. The downstream — frontier
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

## Next
- Closest reachable: Gauss's lemma / the quadratic character of `2` (Open 2), both directly on
  `euler_criterion`.  Or promote first (Open 1).  Or open a different domain (primacy = breadth).

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
