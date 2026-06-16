# Bertrand's postulate — ∅-axiom roadmap (frontier)

**Target:** for every `n ≥ 1` there is a prime `p` with `n < p ≤ 2n`.

**Verdict (multi-agent panel, 2026-06-16):** **fully ∅-axiom-reachable** with the current
DRLT machinery — 213 lacks no fundamental infrastructure.  Erdős's elementary proof runs
entirely through the central binomial coefficient, and the repo already has the engine:
`central_binom_ge_two_pow`, `four_pow_le_succ_mul_central_binom` (`4ⁿ ≤ (2n+1)·C(2n,n)`),
`prime_dvd_central_binom`, Kummer `vp_central_binom_le_floorLog`, the window-product layer
(`primesIn`, `listProd_dvd`, `window_prod_dvd_central_binom`, `window_prod_le`,
`pow_length_le_prod`), plus `IntSqrt.isqrt` (for `√`), `FloorLog` (for `log`), `decPrime`
(the finite chain).  No axiom risk; a multi-week formalization, not an open problem.

## The keystone: the primorial bound `∏_{p≤N} p ≤ 4ⁿ`

The one genuinely missing lemma.  Erdős's proof by strong induction:
- `N` even, `N>2`: `N` not prime, `∏_{p≤N} = ∏_{p≤N−1} ≤ 4^{N−1} ≤ 4ⁿ`.
- `N = 2m+1` odd: `∏_{p≤2m+1} = ∏_{p≤m+1} · ∏_{(m+1, 2m+1]}`; the upper window divides
  `C(2m+1,m) ≤ 4^m`, the lower is `≤ 4^{m+1}` (induction), product `≤ 4^{2m+1}`.

## Landed this session (∅-axiom)

- **`primesIn_split`** / **`listProd_append`** (`MultSystemValue.lean`, Lens) — the window
  split realizing the odd-`N` Erdős decomposition + product multiplicativity.
- **`binom_eq_choose`** (`Lib/Math/NumberTheory/BinomChooseBridge.lean`) — the Lens
  `MultSystem.binom` and Lib `Binomial.choose` are the identical Pascal recursion; proved
  equal, composing the two toolboxes (resolves the layer/def hazard via the `Lens.Number`
  umbrella).
- **`odd_central_binom_le : C(2m+1,m) ≤ 4^m`** (`Lib/Math/NumberTheory/OddCentralBinom.lean`)
  — keystone 2, via `choose_symm` + `pascal_row_sum` + the new sum helpers
  (`term_le_sumTo`, `sumTo_mono_len`, `two_terms_le_sumTo`) + `four_pow_eq` (`4^m = 2^{2m}`,
  pure induction avoiding the propext-tainted `Nat.pow_mul`).

## Remaining sub-bricks (precise)

1. **`prime_dvd_odd_binom`** — primes `p ∈ (m+1, 2m+1]` divide `C(2m+1, m)` — MEDIUM,
   the **next unit**, but now **gated on a second duplicate-def bridge** (confirmed
   2026-06-16): `choose_mul_factorials` is stated over `factorial`, while
   `prime_not_dvd_fact`/`dvd_fact` (the vp argument's inputs) are over `fact` — and the repo
   has **7+ distinct `fact` defs** plus `factorial`.  So the vp argument needs a
   `fact = factorial` bridge first (likely trivial — same recursion — like `binom_eq_choose`).
   The vp tools (`vp_mul`, `le_vp_iff`, `vp_eq_zero_of_not_dvd`) are in `Meta.Nat`, reachable.

   **The real Bertrand blocker is repo-wide def-duplication**, not mathematics: binomial
   (`binom`×4 + `choose`) and factorial (`fact`×7 + `factorial`).  `binom_eq_choose` is one
   bridge; the principled fix is an **`org-audit` def-unification pass** (canonicalize one
   `binom` + one `fact`, re-export via the layer umbrellas), after which `prime_dvd_odd_binom`
   → `window_prod_le_odd` → `primorial_le_four_pow` → full Bertrand are mechanical given the
   landed keystones.  Recommended before resuming the chain.
2. **`window_prod_le_odd`** — `∏_{(m+1,2m+1]} p ≤ C(2m+1,m)` — EASY given 1, via
   `listProd_dvd` + `primesIn_nodup`.
3. **`primorial_le_four_pow`** — the strong induction assembling 1–2 with `primesIn_split`,
   `listProd_append`, `odd_central_binom_le`, `binom_eq_choose`.  Lives in `Lib`
   (cross-layer: Lens `primesIn`/`listProd` + Lib `odd_central_binom_le`).

## Then full Bertrand (HARD, the real grind)

After the primorial: the `(2m/3, m]` vanishing-window lemma, the prime-range partition +
small-prime count via `isqrt`, the final crossover inequality `4^{n/3} > (2n+1)(2n)^{⌊√2n⌋}`
past `N₀ ≈ 468` (pure-`Nat`, watch propext-tainted order lemmas — use the pure
replacements), and the explicit prime-chain finite `decide`
(2,3,5,7,13,23,43,83,163,317,631,1259,2503).  No in-principle obstruction.

(Panel transcript: `/tmp/bertrand_panel.md`.)
