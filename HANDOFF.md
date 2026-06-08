# Session Handoff — 2026-06-08 (closing the p-adic / reciprocity frontier seeds)

## Branch
`claude/p-adic-reciprocity-topics-qBPUW`.  **Seven ∅-axiom closures** (incl. the Zolotarev homomorphism half) committed this session
(all PURE, build clean: `CayleyDickson` + `Linalg213` + `Padic` umbrellas build, new modules
scan 0 DIRTY).

## What Was Done — seven frontier seeds closed (∅-axiom)

The session worked the open-seed list (`research-notes/frontiers/`) across the named topics:
*determinant/sign · p-adic harvest · residue-unit +1 · reciprocity · sums-of-squares · betti ·
euler converse*.  **Three topics fully closed** (determinant/sign, sums-of-squares disc-`−8`,
p-adic harvest) plus the **Zolotarev homomorphism half** (reciprocity); the rest triaged below.
Closures 6–7 (`Zolotarev.lean`) are listed in the reciprocity row of the triage table.

### 1. ★ disc-`−8` representation iff — **sums-of-squares topic CLOSED**
`lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/ZSqrtNegTwoSquare.lean` (11 PURE).
`disc_neg_eight_iff` : `p = a²+2b² ⟺ p ≡ 1,3 (mod 8)` for an odd prime — the `ℤ[√−2]` twin of
`GaussianTwoSquare.two_square_iff`.  Sufficiency (`rep_of_mod8`) supplies the Pillar-I input the
bare non-residue search lacked, via the **Legendre homomorphism** `(−2/p) = (−1/p)·(2/p)`
(`legendre_mul` at `a=p−1`, `b=2`, with `((p−1)·2) % p = p−2`), the factors being the closed
first/second supplements; the characters agree on `p ≡ 1,3 mod 8` ⟹ `p ∣ z²+2` ⟹
`split_form_two`.  Necessity (`mod8_of_rep`) is a square/`2·square`-mod-8 enumeration.

### 2. ★★ `det (permMatrix σ) = psign σ` — **determinant/sign headline CLOSED**
`lean/E213/Lib/Math/Algebra/Linalg213/PermMatrixDet.lean` (8 PURE).  The two readings of a
permutation (matrix vs. inversion-count sign) identified.  Reuses the bubble-sort reduction of
`psign_mul`: an adjacent `swapAt` is a **row swap** of `permMatrix` (`permMatrix_swap_pointwise`),
so `det_swapRows` negates `det` in lockstep with `psign_swapAt`; `descent_of_inv_pos` drives `σ`
to `iota n`, where `det_permMatrix_iota` (lower-triangular, value `1`) meets `psign(iota n) = 1`.

### 3. ★ column Laplace expansion — **determinant/sign seed (b) CLOSED**
`lean/E213/Lib/Math/Algebra/Linalg213/ColumnLaplace.lean` (2 PURE).  `cofactor_col_k` expands
`det` along an arbitrary column, the dual of `cofactor_row_i`, free from `det_transpose`:
`minorAt k j Mᵀ` is **defeq** `transpose (minorAt j k M)` (row-skip = col-skip = `colShift`).

### 4. ★ p-adic multiplicative `ZpSeqEquiv` identities — **p-adic harvest topic CLOSED**
`lean/E213/Lib/Math/NumberSystems/Padic/SetoidMul.lean` (11 PURE).  `mul_{comm,assoc,one,add}`
at the Setoid level + `zp_setoid_comm_ring_capstone` — `ZpSeq` modulo `ZpSeqEquiv` is a
commutative ring.  `Zp.mul_trunc` descends each law to `ℤ/pⁿ` (only `Nat.mul_assoc`'s propext
needed swapping for `ring_nat`), mirroring `SetoidAssoc` for `Zp.add`.

### 5. ★ `i₅ = teichmuller(2-lift)` — **the follow-on it unblocked**
`lean/E213/Lib/Math/NumberSystems/Padic/TeichmullerI5.lean` (5 PURE).  `i₅⁴ ≡ 1` ⟹ Frobenius-fixed
`i₅⁵ ≡ i₅` (clean from `Zp.pow_trunc`, all in `ℤ/5ᵐ`) ⟹ `teichmuller_eq_of_fixed` — the 5-adic
imaginary unit IS the canonical `μ₄` Teichmüller representative of its residue.

Catalog (`STRICT_ZERO_AXIOM.md`), the representation essay
(`theory/essays/synthesis/representation_theorems_one_counting_bound.md`), and the frontier notes
(`sums_of_squares_engines.md`, `euler_criterion_converse.md`, `INDEX.md`) all updated.

## Topic-by-topic status (honest triage)

| Topic | Status |
|---|---|
| **determinant / sign** | **CLOSED** — `det_permMatrix` (a) + `cofactor_col_k` (b).  Only open: relocate the constructive pigeonhole (`firstDup`/`mem_of_card_le`/`cnt_filter_le`) to `Meta` — a *cleanup*, not a closure. |
| **sums-of-squares** | disc-`−8` iff **CLOSED**.  Three-square theorem (`n ≠ 4ᵏ(8m+7)`) stays out of reach ∅-axiom (not multiplicative; classical proof needs Dirichlet AP + ternary genus). |
| **euler converse** | downstream **CLOSED in-repo**: 2-character (`second_supplement`), Gauss's lemma (`gauss_qr`).  Narrative already in `theory/math/numbertheory/quadratic_reciprocity.md`.  Open: Zolotarev (below). |
| **reciprocity** | QR + supplements closed.  **Zolotarev homomorphism half CLOSED** (`ModArith/Zolotarev.lean`, 12 PURE): `mulPerm a p` is a permutation (`mulPerm_mem_perms`), multiplication ↦ composition (`mulPerm_comp`), the sign is multiplicative (`psign_mulPerm_hom`), and a **quadratic residue's permutation is even** (`psign_mulPerm_qr`: the `(a/p)=+1 ⟸ a` QR direction as the sign).  **Residual** (converse, non-residue ⟹ odd): the homomorphism route needs a nontriviality witness `∃a, psign(mulPerm a)=−1` — verified that even `a=p−1` (`psign = (−1)^{(p−1)(p−2)/2} = ((p−1)/p)`) only works for `p≡3 mod 4`; **no universal non-residue witness exists for `p≡1 mod 4`**, so it needs a **primitive root / `(p−1)`-cycle** (no such infra in repo) *or* the **Zolotarev=Gauss block-decomposition** `psign(mulPerm a) = (−1)^{μ_a}` (pairing `x↦p−x` + within-pair swaps at the `μ_a` highs; needs disjoint-transposition-sign machinery in the `psign` framework).  Both multi-file.  Cubic/biquadratic reciprocity is very hard. |
| **p-adic harvest** | **CLOSED**: the multiplicative `ZpSeqEquiv` identities (`SetoidMul`, 11 PURE — `zp_setoid_comm_ring_capstone`: `ZpSeq/ZpSeqEquiv` is a commutative ring) and the follow-on **`i₅ = teichmuller(2-lift)`** (`TeichmullerI5`, 5 PURE).  The note's "high difficulty" was overcautious — `Zp.mul_trunc`/`Zp.pow_trunc` descend everything to `ℤ/pⁿ`.  Remaining open: a `Zp.diagLimit` abstraction (refactor) + generalise the uniqueness engine to `sqrt`. |
| **residue-unit +1** | CLOSED (odometer + Zeckendorf carry); open seed = a *decidable* carry-depth sub-classification (the eventually-periodic / finite-state end) — unassessed this session. |
| **betti α=1** | `b₁ = NS²−1 = 1/α₃` closed; open is conceptual (does `NS²−1` recur in the other forced constants? a `c`-dependent higher `b_k`?) — a synthesis question, not a bounded Lean target. |

## Next (highest-value, in order)
1. **Zolotarev converse** `psign(mulPerm a) = (−1)^{μ_a}` — the homomorphism half is now PURE
   (`Zolotarev.lean`); the residual is the non-residue ⟹ odd direction.  Two routes, both
   multi-file: (a) **primitive-root infrastructure** (`(ℤ/p)*` cyclic — needs Euler `φ` +
   `∑_{d∣n} φ(d) = n` on top of the existing `RootBound.eval_zero` ≤-`d`-roots; then the
   `(p−1)`-cycle of `mulPerm g`), the cleaner and more reusable; or (b) the **Zolotarev=Gauss
   block decomposition** (pairing `x↦p−x`, within-pair swaps at the `μ_a` highs, block-lift
   even) — reuses `fold_perm`/`gauss_qr` but needs general-transposition + disjoint-product
   `psign` lemmas in the `Linalg213` framework.
2. Residue-unit decidable carry-depth (assess `Theory/Raw/Odometer`); `Zp.diagLimit` abstraction.

## Three-tier state
- **No promotions needed**: the determinant/sign narrative lives in
  `theory/essays/algebra/{permutation_sign_as_homomorphism,determinant_as_quotient_characteristic}.md`;
  the disc-`−8` is folded into `representation_theorems_one_counting_bound.md`; euler/QR in
  `theory/math/numbertheory/quadratic_reciprocity.md`.
- **Active frontier board**: `research-notes/frontiers/` — updated this session.

## File Map
```
lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/ZSqrtNegTwoSquare.lean  ← disc-−8 iff (11 PURE, new)
lean/E213/Lib/Math/Algebra/CayleyDickson.lean                            ← +import
lean/E213/Lib/Math/Algebra/Linalg213/PermMatrixDet.lean                  ← det(permMatrix)=psign (8 PURE, new)
lean/E213/Lib/Math/Algebra/Linalg213/ColumnLaplace.lean                  ← column Laplace (2 PURE, new)
lean/E213/Lib/Math/Algebra/Linalg213.lean                                ← +2 imports
STRICT_ZERO_AXIOM.md                                                     ← +3 module entries
theory/essays/synthesis/representation_theorems_one_counting_bound.md    ← disc-−8 closure folded in
research-notes/frontiers/{sums_of_squares_engines,euler_criterion_converse,INDEX}.md  ← status updated
lean/E213/Lib/Math/NumberSystems/Padic/SetoidMul.lean                    ← mul ZpSeqEquiv identities (11 PURE, new)
lean/E213/Lib/Math/NumberSystems/Padic/TeichmullerI5.lean                ← i₅ = teichmuller (5 PURE, new)
lean/E213/Lib/Math/NumberSystems/Padic.lean                              ← +2 imports
```
