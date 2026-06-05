# Session Handoff — 2026-06-05 (Euler's criterion: two halves closed + reframing-lint pilot)

## Branch
`claude/math-frontier-research-6Bw68` — `cd lean && lake build E213.Lib.Math.NumberTheory.ModArith` ✓
clean; both new theorems `#print axioms`-clean (PURE).

## What was done this session

### 1. Euler's criterion — two halves closed (strict ∅-axiom)
New file `lean/E213/Lib/Math/NumberTheory/ModArith/EulerCriterion.lean` (**2 PURE**), wired into the
`ModArith` umbrella:

- `euler_dichotomy` — prime `p`, `2m = p−1`, unit `1 ≤ a < p` ⟹ `p ∣ (aᵐ − 1) ∨ p ∣ (aᵐ + 1)`
  (i.e. `aᵐ ≡ ±1`).  `Y = aᵐ`, `Y² = a^(p−1) ≡ 1` (FLT `universal_flt_main`), factor
  `Y²−1 = (Y−1)(Y+1)`, disjunctive Euclid `nat_prime_dvd_mul` (FourSquareSeed).  The exponent is a
  hypothesis `2m = p−1` (the odd-prime witness) — no division, mirroring `exists_nonfixed`'s `3m = p−1`.
- `euler_qr_pow_one` — `a ≡ x²` (unit `x`) ⟹ `p ∣ (aᵐ − 1)` (residue lands on `+1`):
  `aᵐ ≡ (x²)ᵐ = x^(2m) = x^(p−1) ≡ 1` via `pow_mod_base` + `pow_mul_loc` + FLT.

Together: **residues land on `+1`; every unit is `±1`.**  Foundational brick under Gauss's lemma / the
quadratic character of `2` / Zolotarev (all currently absent from the repo).

### 2. The converse — recorded as a precise frontier
`research-notes/frontiers/euler_criterion_converse.md` — the landmark `aᵐ ≡ 1 ⟺ QR` reduces to a
**squares-list saturation** of `RootBound.eval_zero`: the `m` squares `[i² : i∈1..m]` are `m` distinct
roots of `Xᵐ−1`; a non-residue root would give `m+1` distinct roots of a length-`(m+1)` polynomial →
`eval_zero` forces const `−1 ≡ 0` → contradiction.  Verbatim the `NonFixedExists.exists_nonfixed_gen`
`none`-branch with `S` swapped for the residue range.  **One genuinely new lemma** (`sqList_pairwise`:
`i²−j² = (i−j)(i+j)`, both factors `< p`, Euclid — not the small-abs bound `intRangeFrom_pairwise` uses);
everything else is a transcription.

### 3. Re-framing-lint pilot (agent-side empirical test)
`research-notes/frontiers/the_reframing_conquest.md` updated with the pilot: a CONTROL (no lint) vs
TREATMENT (the CLAUDE.md §0 Residue-lint) subject agent on a 4-question trap battery.  Result
**4/4 → 0/4 reified** — the generation-time output-lint reduced re-framing without degenerating into
blanket hedging (TREATMENT correctly kept Q4's framework-entailed unreachability).  Caveats: N=1/arm,
scorer is a known instance, `0/4 ≠ eliminated` (minimizable-not-eliminable holds in the unbounded limit).

## Open Problems (priority order)

1. **Euler converse** — `research-notes/frontiers/euler_criterion_converse.md`.  Reachable; the only
   non-mechanical step is `sqList_pairwise`.  Closing it gives full Euler `aᵐ ≡ 1 ⟺ QR`.
2. **Then, downstream of Euler** (breadth): quadratic character of `2` (`2` QR ⟺ `p ≡ ±1 mod 8`, the
   second supplement — flagged in `sums_of_squares_engines.md`); Gauss's lemma `(a/p) = (−1)^μ`;
   **Zolotarev** `(a/p) = sign(mul-by-a permutation)` — the `psign` machinery
   (`Algebra/Linalg213/Permutation.lean`, `psign_swap_prefix` PURE) is the sign side, Euler the
   number-theory side.
3. **Reframing-lint** — scale the pilot (N per arm, error bars) + vary battery difficulty to locate where
   re-framing re-emerges (the empirical signature of minimizable-not-eliminable).

## Next
- Closest reachable: the Euler converse (Open 1) → full criterion → second supplement.
- Or open a different domain (primacy = breadth).

## File Map
```
lean/E213/Lib/Math/NumberTheory/ModArith/EulerCriterion.lean   ← euler_dichotomy, euler_qr_pow_one (2 PURE)
lean/E213/Lib/Math/NumberTheory/ModArith.lean                  ← umbrella import added
lean/E213/Lib/Math/NumberTheory/ModArith/NonFixedExists.lean   ← the saturation template (converse)
lean/E213/Lib/Math/NumberTheory/PolyRoot/RootBound.lean        ← eval_zero (Lagrange bound)
lean/E213/Lib/Math/NumberTheory/PolyRoot/ResidueList.lean      ← intRangeFrom / pmoSucc / pairwise pattern
lean/E213/Lib/Math/Algebra/Linalg213/Permutation.lean          ← psign (Zolotarev sign side, PURE)
research-notes/frontiers/euler_criterion_converse.md           ← the open converse + full proof plan
research-notes/frontiers/the_reframing_conquest.md             ← reframing-lint pilot recorded
STRICT_ZERO_AXIOM.md                                           ← Euler 2-PURE section added
```
