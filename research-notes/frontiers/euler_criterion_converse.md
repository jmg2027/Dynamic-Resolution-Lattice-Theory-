# Euler's criterion — the converse (root-count saturation)

**Status (2026-06-05).**  Two halves closed strict ∅-axiom this session in
`lean/E213/Lib/Math/NumberTheory/ModArith/EulerCriterion.lean`:

- `euler_dichotomy` — for prime `p`, `2m = p−1`, unit `1 ≤ a < p`:
  `p ∣ (aᵐ − 1) ∨ p ∣ (aᵐ + 1)`  (i.e. `aᵐ ≡ ±1`).  Route: `Y = aᵐ`, `Y² = a^(p−1) ≡ 1`
  (FLT `universal_flt_main`), factor `Y²−1 = (Y−1)(Y+1)`, disjunctive Euclid `nat_prime_dvd_mul`.
- `euler_qr_pow_one` — `a ≡ x²` (unit `x`) ⟹ `p ∣ (aᵐ − 1)` (the residue lands on the `+1`
  branch).  Route: `aᵐ ≡ (x²)ᵐ = x^(2m) = x^(p−1) ≡ 1` via `pow_mod_base` + `pow_mul_loc` + FLT.

Together: **residues land on `+1`; every unit is `±1`.**  Usable, but the landmark
(`aᵐ ≡ 1 ⟺ a` is a QR; equivalently non-residues land on `−1`) needs the **converse**.

## The converse — proof plan (reachable, mirrors `NonFixedExists`)

Claim: `p` prime, `2m = p−1`, unit `1 ≤ a < p`, `aᵐ ≡ 1 (mod p)` ⟹ `∃ x, x² ≡ a (mod p)`.

The saturation argument (the exact shape of `exists_nonfixed_gen`, run on `Xᵐ − 1` instead of
its negation):

1. **The `m` square-roots.**  `S = [ (i·i : Int) : i ∈ 1..m ]` (length `m`).  Each is a root
   of `Xᵐ − 1` mod `p`: `(i²)ᵐ = i^(2m) = i^(p−1) ≡ 1` (FLT, `i` a unit since `1 ≤ i ≤ m < p`).
   This reuses `pmoSucc (m−1)` (= the coeff list of `Xᵐ − 1`, length `m+1`), `eval_pmoSucc`,
   `eval_pmoSucc_zero` (= `−1`) exactly as `NonFixedExists` does.
2. **`S` is pairwise-distinct mod `p`.**  For `1 ≤ j < i ≤ m`: `i² − j² = (i−j)(i+j)`, with
   `0 < i−j < p` and `0 < i+j ≤ 2m = p−1 < p`, so `p` (prime) divides neither factor →
   `p ∤ (i²−j²)` (Euclid, `int_euclid` / `nat_prime_dvd_mul`).  **This is the one genuinely new
   list lemma** — unlike `intRangeFrom_pairwise`, the differences are products, not small-abs, so
   the bound is Euclid-on-two-factors, not `natAbs < p`.
3. **The closure.**  Suppose `a` is *not* a QR, i.e. `a`'s residue is distinct mod `p` from every
   `i²` in `S`.  Then `S ++ [↑a]` is `m+1` pairwise-distinct roots of `Xᵐ − 1` (length `m+1`),
   so `eval_zero p hp hpr (pmoSucc (m−1)).length (pmoSucc (m−1)) … (S ++ [↑a]) …` forces
   `p ∣ eval (pmoSucc (m−1)) 0 = −1` → `p ≤ 1`, contradiction.  Hence `a` *is* a QR.

### Components needed
- `sqList : Nat → List Int` (`[i·i : i ∈ 1..m]`) + `length = m`, `mem` characterization.
- `sqList_pairwise` — the new Euclid-on-two-factors distinctness (step 2).
- `sqList_roots` — each `i²` a root of `pmoSucc (m−1)` (step 1, reuses `euler_qr_pow_one`'s core).
- `Pairwise (S ++ [↑a])` from `S` pairwise + `a` distinct-from-all (a `List.pairwise_append`
  assembly; `List213` has `nodup_append` — check for a `Pairwise` append analog or inline it).
- Then `eval_zero` closes it (the `NonFixedExists.exists_nonfixed_gen` `none`-branch, verbatim
  modulo `S` for `intRangeFrom`).

Estimated: one focused file; the only non-mechanical step is `sqList_pairwise`.  Everything else
is a transcription of `NonFixedExists` with `S` swapped for the residue range.

## Downstream once the converse lands
- Full Euler's criterion `aᵐ ≡ 1 ⟺ QR`; non-residue ⟹ `aᵐ ≡ −1` (dichotomy + converse).
- **Quadratic character of `2`** (`2` is a QR ⟺ `p ≡ ±1 mod 8`) — the second supplement,
  flagged open in `sums_of_squares_engines.md`; classical proof = Gauss's lemma count, which Euler
  feeds.
- **Gauss's lemma** `(a/p) = (−1)^μ` (the `μ`-count bridge).
- **Zolotarev** `(a/p) = sign(mul-by-a permutation)` — the `psign` machinery
  (`Algebra/Linalg213/Permutation`, `psign_swap_prefix` already PURE) supplies the sign side; the
  number-theoretic side routes through Euler.

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/EulerCriterion.lean` (the two closed halves),
`…/ModArith/NonFixedExists.lean` (the saturation template),
`…/PolyRoot/RootBound.lean` (`eval_zero`), `…/PolyRoot/ResidueList.lean` (`intRangeFrom`,
`pmoSucc`, the pairwise pattern), `…/FourSquareSeed.lean` (`nat_prime_dvd_mul`),
`…/Algebra/Linalg213/Permutation.lean` (`psign`, for the Zolotarev downstream).
