# Session Handoff — 2026-06-08 (closing the p-adic / reciprocity frontier seeds)

## Branch
`claude/p-adic-reciprocity-topics-qBPUW`.  **Eight ∅-axiom closures** (incl. the Zolotarev homomorphism half + the multiplicative-order foundation) committed this session
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

## ★ Primitive-root marathon (route a → full Zolotarev) — IN PROGRESS

The committed-to multi-session build of `(ℤ/p)*` cyclic ⟹ Zolotarev nontriviality witness.
**Bricks done (all PURE):**
- **brick 0** `MulOrder.lean` (12) — `ordModP`, `fermat`, `pow_ord`, `ord_min`,
  `ord_dvd` (`aᵏ≡1 ⟹ ord∣k`), `ord_dvd_p_sub_one`.
- **brick 1** `Lcm213.lean` (11) — ℕ `lcm` + universal property `lcm_dvd` **without Bezout**
  (`gcd_div_coprime` + `euclid_of_coprime`), `gcd_mul_lcm` (`g·lcm = a·b`).
- **brick 2** `OrderPow.lean` (3) — `ord_mod_eq` (order depends only on base mod `p`) + ★
  `ord_pow` (`ord(aᵏ) = ord(a)/gcd(ord(a),k)`).
- **brick 3** `CoprimeOrder.lean` (1+2) — ★ `ord_mul_coprime`
  (`gcd(ord a, ord b) = 1 ⟹ ordModP ((a·b)%p) p = ord a · ord b`), via the product collapse +
  `euclid_of_coprime` + brick 1's `coprime_mul_dvd` (`lcm_dvd` + `gcd_mul_lcm`).

- **brick 4a** `MaxOrder.lean` (13) — `maxOrd p` (max of `ordModP a p` over `[1,p−1]`) + pure
  `nmax`; `maxOrd_ge`, ★★ `maxOrd_achieved` (`= ordModP g p`, some unit `g`), `one_le_maxOrd`,
  `maxOrd_le_pred` (`1 ≤ maxOrd ≤ p−1`).  The exponent-argument scaffolding.

- **brick 4b-i** `Meta/Nat/Valuation.lean` (15) — the `q`-adic valuation `vp q n` (largest `k`
  with `qᵏ∣n`): `pow_vp_dvd`, `vp_ge`, `vp_not_dvd_succ` (exactness), `le_vp_iff`.  (Core `Nat`
  dvd/mod API is propext-tainted — decides on `n%qᵏ=0` + pure dvd helpers throughout.)
- **brick 4b-ii** `QPart.lean` (6) — `qpart q n := q^(vp q n)`; `qpart_dvd`, `qpart_pos`,
  `gcd_eq_of_dvd` (`b∣a ⟹ gcd a b = b`), `q_not_dvd_quot` (`q∤(n/qpart)`),
  `gcd_qpow_qfree` (`gcd(qᵉ,B)=1` for `q` prime, `q∤B`).
- **brick 4b-iii** `ValuationAlg.lean` (5) — `vp_mul` (`vp q(a·b)=vp q a+vp q b`); ★★★
  `exists_prime_vp_gt` (`α∤d ⟹ ∃ prime q, vp q α > vp q d`, via `gcd_div_coprime` ⟹
  `vp(d/g)=0`).  Plus `vp_eq_of`/`vp_eq_zero`/`one_le_vp`.  *(`OrderPow.not_dvd_pow` exposed
  this session for 4b-iv.)*

- **brick 4b-iv** `EveryOrdDvdMax.lean` (3) — ★★★★ `every_ord_dvd_maxOrd` (THE EXPONENT
  ARGUMENT, the crux): for a unit `a`, `ordModP a p ∣ maxOrd p`.  Pure proof-by-contradiction
  via the decidable `maxOrd % ord = 0` (no Classical `by_contra`).  **The exponent argument /
  every-order-divides-maxOrd is now CLOSED — the hardest part of the marathon is done.**

- **brick 5** `PrimitiveRoot.lean` (9) — ★★★ `maxOrd_eq_pred` (`maxOrd p = p−1`, via
  `RootBound.eval_zero` on `pmoSucc(maxOrd−1) = X^maxOrd−1` with the `p−1` distinct units
  `segInt 1 (p−1)`, each a root by `pow_maxOrd_eq_one`); ★★★★ `exists_primitive_root`
  (`∃ g, 1 ≤ g ≤ p−1 ∧ ordModP g p = p−1`).  **Primitive-root existence CLOSED.**

**Brick remaining (the final combinatorial assembly):**
- **brick 6 — `(p−1)`-cycle ⟹ full Zolotarev** (~200 lines).  Two parts:
  - **(a) the nontriviality sign** `psign (mulPerm g p) = −1` for a primitive root `g`.
    `mulPerm g` (`σ(k)=g·k mod p`) is conjugate to the **cyclic shift** on `{1,…,p−1}` via the
    discrete-log list `τ = [g⁰%p, g¹%p, …, g^{p−2}%p]` (`mulPerm g ≈ τ ∘ shift ∘ τ⁻¹`, so
    `psign(mulPerm g) = psign(shift)` by `PermSign.psign_mul` + `psign_inv`); the cyclic shift
    `[1,2,…,p−2,0]` has `p−2` inversions ⟹ `psign = (−1)^{p−2} = −1` (`p` odd).  (Or: directly
    show `mulPerm g` is one `(p−1)`-cycle and add a "sign of an `n`-cycle = `(−1)^{n−1}`" lemma to
    the `psign` framework.)
  - **(b) extend to all residues**: `φ(a) := psign(mulPerm a)` is a hom killing squares
    (`Zolotarev.psign_mulPerm_hom`/`_qr`), and `φ(g) = −1` ⟹ `φ = Legendre`; for a non-residue
    `a = g^k` (`k` odd), `φ(a) = φ(g)^k = −1 = (a/p)` (via `mulPerm_comp` iterated + the
    discrete-log/QR characterisation `a` QR ⟺ `k` even).  ⟹ **`psign(mulPerm a) = (a/p)`** for
    all units — the **Zolotarev converse** ⟹ the full Zolotarev/Legendre iff.
- **brick 5 — `RootBound` gluing**: every unit satisfies `x^{maxOrd} ≡ 1`, so `X^{maxOrd}−1`
  (as `List Int`) has `p−1` distinct roots; `RootBound.eval_zero` ⟹ `f ≡ 0` everywhere ⟹
  `f(0) = −1 ≡ 0`, contra ⟹ `p−1 ≤ maxOrd`; with `maxOrd ∣ p−1` ⟹ `maxOrd = p−1` ⟹
  `∃ g, ordModP g p = p−1` (primitive root).
- **brick 6 — cycle**: `mulPerm g` is a single `(p−1)`-cycle (powers of `g` exhaust the
  nonzero residues), `psign = (−1)^{p−2} = −1`; `g` a non-residue ⟹ the **nontriviality
  witness**, and with `Zolotarev.psign_mulPerm_hom`/`_qr` ⟹ full `psign(mulPerm a) = (a/p)`.

## Next (other threads)
- Residue-unit decidable carry-depth (assess `Theory/Raw/Odometer`); `Zp.diagLimit` abstraction.

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
