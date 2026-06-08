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

3. **Zolotarev** `(a/p) = sign(x ↦ a·x mod p)`.  The **matrix/sign side is now fully PURE**:
   `PermMatrixDet.det_permMatrix` (`det (permMatrix σ) = psign σ`) closed this arc, and `psign`
   itself was already PURE.  The remaining gap is the *number-theoretic* identification
   `psign [a·0, a·1, …, a·(p−1) mod p] = (a/p)` — tying the sign of the explicit
   multiplication-by-`a` value-list to the Legendre symbol.  Needs: (a) the mul-map is a
   permutation of the residues (injectivity via the modular inverse + the `List213` `Nodup`
   cardinality toolkit), (b) its `psign` = `(a/p)` (cycle-structure or, more directly, a
   Gauss-lemma bridge — `gauss_core`'s sign product is the same `μ`-parity that Zolotarev's
   transposition count must reproduce).  This bridge (Zolotarev = Gauss) is the genuinely hard
   residual; both endpoints are closed, the equivalence of the two sign-readouts is not.

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/{EulerCriterion,EulerConverse}.lean`,
`…/ModArith/NonFixedExists.lean` (the saturation template),
`…/PolyRoot/RootBound.lean` (`eval_zero`), `…/PolyRoot/{ResidueList,CyclotomicPoly}.lean`,
`…/FourSquareSeed.lean` (`nat_prime_dvd_mul`),
`…/Algebra/Linalg213/Permutation.lean` (`psign`, the Zolotarev sign side),
`Meta/Tactic/List213.lean` (`Nodup` cardinality, for the mul-permutation).
