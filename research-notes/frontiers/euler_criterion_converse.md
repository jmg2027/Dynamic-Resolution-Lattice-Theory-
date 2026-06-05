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

## Open downstream (each builds directly on `euler_criterion`)

1. **Quadratic character of `2`** (the second supplement): `2` is a QR mod `p` ⟺ `p ≡ ±1 (mod 8)`.
   Classical proof = Gauss's lemma count for `a = 2` (`μ = #{x ∈ 1..(p−1)/2 : 2x > p/2}`, a floor
   formula whose parity gives `±1`).  Flagged in `sums_of_squares_engines.md`.  Needs Gauss's lemma
   first (item 2), or a direct `(2)^((p−1)/2)`-evaluation via a telescoping product.
2. **Gauss's lemma** `(a/p) = (−1)^μ`, `μ = #{x ∈ 1..(p−1)/2 : (a·x mod p) > p/2}`.  Bridges Euler's
   `aᵐ ≡ ±1` to a **counting** readout — the `least-absolute-residue` sign count.  The `±1` is exactly
   `euler_dichotomy`; the new content is the `μ`-count = the sign of the half-system permutation.
3. **Zolotarev** `(a/p) = sign(x ↦ a·x mod p)`.  The **sign side is already PURE**
   (`Algebra/Linalg213/Permutation.lean`: `psign`, `psign_swap_prefix`, the inversion-count sign);
   the number-theoretic side routes through Euler (`a` a QR ⟺ `aᵐ ≡ 1` ⟺ the mul-permutation is even).
   The missing piece is `sign(mul-by-a permutation) = aᵐ`-valued — i.e. tie `psign` of the explicit
   value-list `[a·0, a·1, …, a·(p−1) mod p]` to the Legendre symbol.  Needs: (a) the mul-map is a
   permutation of the residues (injectivity via the modular inverse + the `List213` `Nodup`
   cardinality toolkit), (b) its `psign` = `(a/p)` (cycle-structure or Gauss-lemma bridge).

## Cross-references
`lean/E213/Lib/Math/NumberTheory/ModArith/{EulerCriterion,EulerConverse}.lean`,
`…/ModArith/NonFixedExists.lean` (the saturation template),
`…/PolyRoot/RootBound.lean` (`eval_zero`), `…/PolyRoot/{ResidueList,CyclotomicPoly}.lean`,
`…/FourSquareSeed.lean` (`nat_prime_dvd_mul`),
`…/Algebra/Linalg213/Permutation.lean` (`psign`, the Zolotarev sign side),
`Meta/Tactic/List213.lean` (`Nodup` cardinality, for the mul-permutation).
