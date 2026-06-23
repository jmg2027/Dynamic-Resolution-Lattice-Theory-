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

## The factorization crux (item 11) — ✅ **CLOSED ∅-axiom (2026-06-23)**

The Erdős upper bound needs `C(2n,n)` written as an *explicit product of prime
powers over a fixed index set*, so it can be split by the size of `p` and bounded
range by range.  The flat-list `factorization_exists` (no exponents/index set) and
the divisibility lemmas (`listProd_dvd`, `window_prod_dvd_central_binom`, which
bound sub-products *from below*) could not give this.  Now closed:

- **`PrimePowFactorization.prod_prime_pow_eq`** (6/0 PURE): `0 < m → (∀ q prime,
  q ∣ m → q ≤ B) → m = primePowProd (vp · m) (primesIn 0 B)` — the explicit FTA
  product form `m = ∏_{p ≤ B, prime} p^{vₚ(m)}`.  Proof via `vp_separation`
  (equal `vp` at every prime ⟹ equal), with two targeted lemmas
  (`vp_primePowProd_mem`/`_not_mem`) computing `vₚ` of the product on a `Nodup`
  prime list and `mem_primesIn` (converse membership).  `primePowProd` is a direct
  recursion (no `List.map`), with `primePowProd_append` (`∏_{xs++ys} = ∏_xs·∏_ys`)
  for the size split.
- **`CentralBinomFactorization.central_binom_factorization`** (2/0 PURE): `1 ≤ n →
  C(2n,n) = primePowProd (vp · C(2n,n)) (primesIn 0 (2n))`, the index set pinned by
  `central_binom_prime_factors_le` (every prime factor of `C(2n,n)` is `≤ 2n`, from
  `prime_pow_vp_central_binom_le`).

This is the object the remaining items bound by size-ranges.

## Remaining for full Bertrand (keystone + factorization crux now done)

With the primorial bound `∏_{p≤N} p ≤ 4ᴺ` and the explicit factorization
`C(2n,n) = ∏_{p≤2n} p^{vₚ}` both closed, the Erdős proof needs only the
"upper" half: assume no prime in `(n, 2n]`; bound `C(2n,n)` by primes `≤ 2n/3` (whose
product is `≤ 4^{2n/3}` by the primorial) times the `√(2n)`-bounded prime-power tail
(Kummer `vp ≤ ⌊log_p 2n⌋`); contradict the lower bound `4ⁿ/(2n+1) ≤ C(2n,n)`.  Pieces:

1. ~~**The `(2n/3, n]` vanishing window**~~ — ✅ **CLOSED ∅-axiom (2026-06-16)**:
   `BertrandWindow.prime_not_dvd_central_binom_mid` — for prime `p` with `2n/3 < p ≤ n`,
   `p² > 2n`, Legendre gives `vₚ(C(2n,n)) = ⌊2n/p⌋ − 2⌊n/p⌋ = 2 − 2 = 0`, so `p ∤ C(2n,n)`.
   Built on the closed `Legendre.legendre` + the pure floor lemma `NatDiv213.div_eq_of_sandwich`
   (`⌊n/p⌋=1`, `⌊2n/p⌋=2`) + `Nat.div_eq_of_lt` (higher powers vanish) + the new
   `sumTo_eq_first`.  **All component lemmas for Erdős's Bertrand are now ∅-axiom.**
2. **The prime-range partition + small-prime / `√` tail** — split primes `≤ 2n` into
   `≤ 2n/3` (primorial-bounded), `(2n/3, n]` (vanish), `(n, 2n]` (the assumed-empty window),
   with the `≤ √(2n)` primes contributing `≤ (2n)` each (`IntSqrt.isqrt`).  MEDIUM.
   **The per-range bound inputs are now ∅-axiom (2026-06-23):**
   - small range `p ≤ √(2n)`: `PrimePowFactorization.primePowProd_le_pow_length`
     (block `≤ B^{#bases}`) + `primesIn_length_le` (`#bases ≤ √(2n)`) +
     `prime_pow_vp_central_binom_le` (each `p^{vₚ(C)} ≤ 2n`);
   - medium range `√(2n) < p ≤ 2n/3`: `primePowProd_le_listProd` (block `≤ ∏ p`) +
     `CentralBinomFactorization.central_binom_pow_le_self` (`2n < p² ⟹ p^{vₚ(C)} ≤ p`,
     via `vp_central_binom_le_one`) + the primorial bound (`∏ p ≤ 4^{2n/3}`);
   - `primePowProd_append` + `primesIn_split` give the index split.
   What remains in item 2 is *wiring* these together (under the `(n,2n]`-empty hypothesis,
   with the `(2n/3,n]` vanishing window zeroing that block) into `C(2n,n) ≤ (2n)^{√(2n)}·4^{2n/3}`.
3. **The crossover** `4^{n/3} > (2n+1)·(2n)^{⌊√2n⌋}` for `n ≥ N₀ ≈ 468` (pure-`Nat` grind;
   use the pure order-lemma replacements).  HARD — the real work.
4. **The finite prime chain** `2,3,5,7,13,23,43,83,163,317,631,1259,2503` covering `n < N₀`
   (`decide` on primality + the doubling gaps).  MEDIUM, tedious.

**All component lemmas are now ∅-axiom** (primorial keystone + binom/fact bridges +
odd-central bound + the `(n,2n]` and `(2n/3,n]` window facts + the explicit factorization
+ all per-range product bounds).  What remains is the **assembly wiring** (item 2 tail), then
the crossover inequality (item 3 — the hard pure-`Nat` asymptotic) + the finite chain (item 4).
No new mathematical ingredient; no in-principle obstruction.

## Built this session (2026-06-23) — the factorization + size-decomposition layer

New ∅-axiom modules under `Lib/Math/NumberTheory/`:
- `PrimePowFactorization.lean` (10/0): `prod_prime_pow_eq` (explicit FTA product form),
  `primePowProd`(+`_pos`/`_append`), `vp_primePowProd_mem`/`_not_mem`, `mem_primesIn`,
  and the range bounds `primePowProd_le_pow_length`, `primePowProd_le_listProd`,
  `primesIn_length_le`.
- `CentralBinomFactorization.lean` (4/0): `central_binom_factorization`
  (`C(2n,n) = ∏_{p≤2n} p^{vₚ}`), `central_binom_prime_factors_le`, `vp_central_binom_le_one`,
  `central_binom_pow_le_self`.

(Panel transcript: `/tmp/bertrand_panel.md`.)
