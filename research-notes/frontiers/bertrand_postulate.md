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

## Landed this session (∅-axiom, `MultSystemValue.lean`)

- **`primesIn_split`** — `lo ≤ mid ≤ hi → primesIn lo hi = primesIn mid hi ++ primesIn lo mid`
  (the window split realizing the odd-`N` Erdős decomposition).
- **`listProd_append`** — `∏(xs ++ ys) = ∏xs · ∏ys` (so the split multiplies).

## Remaining sub-bricks (precise)

1. **`odd_central_binom_le : C(2m+1, m) ≤ 4^m`** — MEDIUM, **gated on a def-unification
   hazard**.  Mathematically: binom symmetry `C(2m+1,m) = C(2m+1,m+1)` (have: `choose_symm`)
   + the row-sum `C(2m+1,m)+C(2m+1,m+1) ≤ 2^{2m+1}` (have: `binomSum a n` with `a=1` gives
   `Σ_k C(n,k) = 2ⁿ` in `BinomialTheorem`), giving `2·C(2m+1,m) ≤ 2·4^m`.  **Hazard:** the
   central-binomial machinery uses `MultSystem.binom`, while `choose_symm`/`binomSum` use a
   *different* `choose` (`DyadicFSM/FLT/Binomial`) — and there are **four** `binom` defs in
   the repo (`MultSystem`, `Simplex.Counts`, `GenerationCount`, `DepthPRecursiveInstances`)
   with **no proven bridges**.  So the real first step is a `binom_eq_choose` bridge (or
   reproving the row-sum in `MultSystem.binom`), an *integration* task, not the math.  A
   repo-organization opportunity: unify the binomial defs (`org-audit` candidate).
2. **`prime_dvd_odd_binom`** — primes `p ∈ (m+1, 2m+1]` divide `C(2m+1, m)` — MEDIUM,
   mirrors `prime_dvd_central_binom` (`vp_p = 1`: `p ≤ 2m+1 < 2p`, `p > m+1` so `p ∤ m!`,
   `p ∤ (m+1)!`).
3. **`window_prod_le_odd`** — `∏_{(m+1,2m+1]} p ≤ C(2m+1,m)` — EASY given 1,2, via
   `listProd_dvd` + `primesIn_nodup` (exactly the `window_prod_dvd_central_binom` pattern,
   now with `primesIn_split` available).
4. **`primorial_le_four_pow : listProd (primesIn 0 N) ≤ 4^N`** — the strong induction
   assembling 1–3 with `primesIn_split` + `listProd_append`.  New file
   `Lens/Number/Nat213/Primorial.lean`.

## Then full Bertrand (HARD, the real grind)

After the primorial: the `(2m/3, m]` vanishing-window lemma, the prime-range partition +
small-prime count via `isqrt`, the final crossover inequality `4^{n/3} > (2n+1)(2n)^{⌊√2n⌋}`
past `N₀ ≈ 468` (pure-`Nat`, watch propext-tainted order lemmas — use the pure
replacements), and the explicit prime-chain finite `decide`
(2,3,5,7,13,23,43,83,163,317,631,1259,2503).  No in-principle obstruction.

(Panel transcript: `/tmp/bertrand_panel.md`.)
