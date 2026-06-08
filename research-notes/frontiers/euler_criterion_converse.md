# Euler's criterion — CLOSED; the downstream (2-character, Gauss, Zolotarev)

**Status (2026-06-05).**  Euler's criterion is **closed strict ∅-axiom**
(`lean/E213/Lib/Math/NumberTheory/ModArith/{EulerCriterion,EulerConverse}.lean`, 16 PURE):

- `euler_dichotomy` — `aᵐ ≡ ±1 (mod p)` (`2m = p−1`).
- `euler_qr_pow_one` — `a ≡ x²` ⟹ `aᵐ ≡ 1` (residue → `+1`).
- `euler_converse` — `aᵐ ≡ 1` ⟹ `a` a QR (squares-list saturation of `RootBound.eval_zero`).
- ★ `euler_criterion` — the **full iff** `aᵐ ≡ 1 ⟺ a` is a quadratic residue.

The converse's one new idea was `sq_diff_not_dvd` (`i²−j² = (i−j)(i+j)`, both factors in `(0,p)`,
Euclid); the rest transcribed `NonFixedExists.exists_nonfixed_gen` with the squares window `sqFrom`
replacing the residue range.  This sub-tree is **promotion-eligible** (closed + categorical) — write
`theory/math/numbertheory/euler_criterion.md` and archive this note.

## Downstream — closed so far

- **First supplement** `−1` QR ⟺ `p ≡ 1 (mod 4)` — **CLOSED** (`EulerFirstSupplement.neg_one_qr_iff`,
  4 PURE): `euler_criterion` at `a = p−1` + parity of `(−1)ᵐ`.
- **Legendre multiplicativity** `QR(ab) ⟺ (QR(a) ⟺ QR(b))` — **CLOSED**
  (`LegendreMultiplicative.legendre_mul`, 5 PURE): `qr_iff_pow_one` + `cᵐ ≡ ±1` + `(ab)ᵐ ≡ aᵐbᵐ`,
  2×2 sign cases.  The Legendre character is a homomorphism.

## Downstream — now closed

1. **Quadratic character of `2`** (the second supplement): `2` is a QR mod `p` ⟺ `p ≡ ±1 (mod 8)`
   — **CLOSED** (`SecondSupplement.second_supplement`, via the Gauss-lemma `μ`-count for `a = 2`).
   And the disc-`−8` representation iff (`ZSqrtNegTwoSquare.disc_neg_eight_iff`) is built on it.
2. **Gauss's lemma** `(a/p) = (−1)^μ`, `μ = #{x ∈ 1..(p−1)/2 : (a·x mod p) > p/2}` — **CLOSED**
   (`GaussLemma.gauss_qr`/`gauss_core`, the half-system `fold_perm` + sign product `gauss_core`).

## Open downstream

3. **Zolotarev** `(a/p) = sign(x ↦ a·x mod p)`.  **Homomorphism half CLOSED**
   (`ModArith/Zolotarev.lean`, 12 PURE): `mulPerm a p = [a·0,…,a·(p−1) mod p]` is a permutation
   (`mulPerm_mem_perms`, injectivity via `res_cancel` + the `nodup_imp_perm` toolkit);
   multiplication becomes composition (`mulPerm_comp`: `composeList (mulPerm a)(mulPerm b) =
   mulPerm ((a·b)%p)`, both `getD i = (a·b·i)%p`); hence the **sign is multiplicative**
   (`psign_mulPerm_hom`, via `psign_mul`) and a **quadratic residue's permutation is even**
   (`psign_mulPerm_qr`/`psign_mulPerm_qr_pred`: `mulPerm (z²) = mulPerm z ∘ mulPerm z`,
   `psign = psign(mulPerm z)² = 1`) — the `(a/p)=+1 ⟸ a` QR direction realised as the sign.
   **Remaining residual** (the converse, non-residue ⟹ odd permutation): the clean homomorphism
   route needs a *nontriviality witness* (`∃a, psign(mulPerm a) = −1`), which requires a
   **primitive root / `(p−1)`-cycle** (no universal non-residue witness for `p ≡ 1 mod 4`) — the
   repo has no primitive-root infrastructure; *or* the direct **Zolotarev = Gauss** count
   `psign(mulPerm a) = (−1)^{μ_a}` via the pairing/block decomposition (`x ↦ p−x` pairs the
   residues, mul permutes the `m` pairs by `fold_a` with within-pair swaps at the `μ_a` "high"
   positions; block-lifts are even ⟹ sign `(−1)^{μ_a}`), then `gauss_qr`.  Both are multi-file
   undertakings (the block-decomposition needs disjoint-transposition-sign machinery in the
   `psign` framework).

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/{EulerCriterion,EulerConverse}.lean`,
`…/ModArith/NonFixedExists.lean` (the saturation template),
`…/PolyRoot/RootBound.lean` (`eval_zero`), `…/PolyRoot/{ResidueList,CyclotomicPoly}.lean`,
`…/FourSquareSeed.lean` (`nat_prime_dvd_mul`),
`…/Algebra/Linalg213/Permutation.lean` (`psign`, the Zolotarev sign side),
`Meta/Tactic/List213.lean` (`Nodup` cardinality, for the mul-permutation).
