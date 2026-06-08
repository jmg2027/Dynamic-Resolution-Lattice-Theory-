# Session Handoff — 2026-06-08 (closing the p-adic / reciprocity frontier seeds)

## Branch
`claude/p-adic-reciprocity-topics-qBPUW`.  Three ∅-axiom closures committed this session
(all PURE, build clean: `CayleyDickson` + `Linalg213` umbrellas build, new modules scan
0 DIRTY).

## What Was Done — three frontier seeds closed (∅-axiom)

The session worked the open-seed list (`research-notes/frontiers/`) across the named topics:
*determinant/sign · p-adic harvest · residue-unit +1 · reciprocity · sums-of-squares · betti ·
euler converse*.  Two topics are now closed; the rest are triaged below.

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

Catalog (`STRICT_ZERO_AXIOM.md`), the representation essay
(`theory/essays/synthesis/representation_theorems_one_counting_bound.md`), and the frontier notes
(`sums_of_squares_engines.md`, `euler_criterion_converse.md`, `INDEX.md`) all updated.

## Topic-by-topic status (honest triage)

| Topic | Status |
|---|---|
| **determinant / sign** | **CLOSED** — `det_permMatrix` (a) + `cofactor_col_k` (b).  Only open: relocate the constructive pigeonhole (`firstDup`/`mem_of_card_le`/`cnt_filter_le`) to `Meta` — a *cleanup*, not a closure. |
| **sums-of-squares** | disc-`−8` iff **CLOSED**.  Three-square theorem (`n ≠ 4ᵏ(8m+7)`) stays out of reach ∅-axiom (not multiplicative; classical proof needs Dirichlet AP + ternary genus). |
| **euler converse** | downstream **CLOSED in-repo**: 2-character (`second_supplement`), Gauss's lemma (`gauss_qr`).  Narrative already in `theory/math/numbertheory/quadratic_reciprocity.md`.  Open: Zolotarev (below). |
| **reciprocity** | QR + supplements closed.  **Zolotarev** now has *both endpoints* PURE — the sign side `det_permMatrix`/`psign`, the count side `gauss_core`'s `μ`-parity — but the **equivalence of the two sign-readouts** (`psign[a·0,…,a·(p−1) mod p] = (a/p)`) is the genuinely hard residual.  Cubic/biquadratic reciprocity over `ℤ[ω]/ℤ[i]` is very hard. |
| **p-adic harvest** | `i₅ = teichmuller(2-lift)` is **blocked** on the open *multiplicative `ZpSeqEquiv` identities* (mul comm/assoc at the trunc/sequence level): `i₅⁴ ≡ 1` exists (`i_5_pow_four_trunc`) but relating `pow i₅ 4` (left-nested) to it needs trunc-level associativity, which is itself an open seed (G123 §C, flagged high-difficulty / possibly not 213-native). |
| **residue-unit +1** | CLOSED (odometer + Zeckendorf carry); open seed = a *decidable* carry-depth sub-classification (the eventually-periodic / finite-state end) — unassessed this session. |
| **betti α=1** | `b₁ = NS²−1 = 1/α₃` closed; open is conceptual (does `NS²−1` recur in the other forced constants? a `c`-dependent higher `b_k`?) — a synthesis question, not a bounded Lean target. |

## Next (highest-value, in order)
1. **Zolotarev bridge** `psign[a·x mod p] = (a/p)` — both endpoints PURE; the missing piece is
   tying the mul-by-`a` permutation's `psign` to `gauss_core`'s `μ`-parity (the mul-map is a
   permutation via the modular inverse + `List213.Nodup`; then `psign = (−1)^μ`).  The one
   genuinely-tractable hard target left, and it spans reciprocity + euler-converse.
2. **p-adic multiplicative trunc identities** (`Zp.mul_comm`/`mul_assoc`/`mul_one` at trunc) —
   the gateway that unblocks `i₅ = teichmuller` and the `ω·u` sequence-level split.
3. Residue-unit decidable carry-depth (assess `Theory/Raw/Odometer`).

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
```
