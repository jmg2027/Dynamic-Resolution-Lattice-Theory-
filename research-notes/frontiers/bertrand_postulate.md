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

## The keystone: the primorial bound `∏_{p≤N} p ≤ 4ⁿ` — ✅ **CLOSED ∅-axiom (2026-06-16)**

`Primorial.primorial_le_four_pow` (PURE).  Erdős's strong induction with the parity split:
even `N=2q` reuses the existing `window_prod_le` (primes in `(q,2q]`, `≤ 2^{2q}=4^q`) + IH(`q`);
odd `N=2q+1` uses `window_prod_le_odd` (`≤ 4^q`) + IH(`q+1`); both close to `4ᴺ` via the pure
`pow_add` + parity arithmetic.  No compositeness lemma needed (the even case uses the binomial
window, not "N composite").  The full supporting chain landed this session:

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
- **`prime_dvd_odd_binom`**, **`window_prod_le_odd`**, **`primorial_le_four_pow`**
  (`Lib/Math/NumberTheory/Primorial.lean`) — the divisibility (vp argument over the
  `fact = factorial` bridge), the window bound, and the primorial induction.  **Keystone CLOSED.**

## Remaining for full Bertrand (the keystone is done)

With the primorial bound `∏_{p≤N} p ≤ 4ᴺ` closed, the Erdős proof needs only the
"upper" half: assume no prime in `(n, 2n]`; bound `C(2n,n)` by primes `≤ 2n/3` (whose
product is `≤ 4^{2n/3}` by the primorial) times the `√(2n)`-bounded prime-power tail
(Kummer `vp ≤ ⌊log_p 2n⌋`); contradict the lower bound `4ⁿ/(2n+1) ≤ C(2n,n)`.  Pieces:

1. **The `(2n/3, n]` vanishing window** — primes there do not divide `C(2n,n)`
   (`vp = 0`: `p > 2n/3` and `2p ≤ 2n < 3p` give exactly one factor in numerator and one
   in each `n!`, cancelling).  MEDIUM.
2. **The prime-range partition + small-prime / `√` tail** — split primes `≤ 2n` into
   `≤ 2n/3` (primorial-bounded), `(2n/3, n]` (vanish), `(n, 2n]` (the assumed-empty window),
   with the `≤ √(2n)` primes contributing `≤ (2n)` each (`IntSqrt.isqrt`).  MEDIUM.
3. **The crossover** `4^{n/3} > (2n+1)·(2n)^{⌊√2n⌋}` for `n ≥ N₀ ≈ 468` (pure-`Nat` grind;
   use the pure order-lemma replacements).  HARD — the real work.
4. **The finite prime chain** `2,3,5,7,13,23,43,83,163,317,631,1259,2503` covering `n < N₀`
   (`decide` on primality + the doubling gaps).  MEDIUM, tedious.

No in-principle obstruction; the keystone (the part that needed the binom/fact bridges) is done.

(Panel transcript: `/tmp/bertrand_panel.md`.)
