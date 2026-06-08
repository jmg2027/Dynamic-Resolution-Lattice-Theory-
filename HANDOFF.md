# Session Handoff — 2026-06-07 (b)

## Branch
`claude/leibniz-determinant-perms-5zT6T` — pushed.
`cd lean && lake build` ✓ clean (full tree); `tools/layer_audit.py` 0 violations.
All new theorems ∅-axiom PURE.

## What Was Done This Session

Picked up the two open frontiers in
`research-notes/frontiers/count_substrate_synthesis.md` — both now closed.

### 1. Meta/Nat strict-order/pow suite — CLOSED
The canonical propext-free forms are now all in `Meta/Nat`:
- `NatRing213.nat_mul_lt_mul_right` / `_left` / `mul_lt_mul_left_pure` (strict-mono)
- `PureNat.pow_add` (general base `a^(m+n) = a^m·a^n`)
- ★ **`NatRing213.nat_succ_sub`** (NEW) — `(n+1)−m = (n−m)+1` for `m ≤ n`.
Dropped the scattered private `SpernerChains.succ_sub_clean` in favour of it.
Core `Nat.succ_sub` carries `propext`; `Nat.mul_lt_mul_right` carries
`propext`+`Classical.choice`+`Quot.sound` — all displaced.

### 2. Leibniz determinant over `perms` — FULLY CLOSED (bridge built)
The Leibniz determinant was **already complete** from prior work (the stale
handoff "no enumeration" framing was wrong): `Permutation.leibDet`, `PermClosure`
(sound/complete/nodup, `perms_swap_closed`, `leibDet_rowSwap` alternating,
equal-rows ⟹ 0, multilinearity), `Laplace` (cofactor expansion, `leibDet_eq_det`,
adjugate `M·adj M = det·I`), downstream `CayleyHamilton` + `CharPolyAdj`.

The genuinely-missing piece — **the bridge between the two permutation
developments** — is now built: `lean/E213/Lib/Math/Algebra/Linalg213/PermBridge.lean`
(7/7 PURE):
- `flatMap_eq` / `cflatMap_congr` (funext-free) / `insEv_eq`
- ★ `permsOf_eq` — `Permutation.permsOf xs = Combinatorics.Permutations.perms xs`
  (same list; flatMap213 vs core flatMap concatenate identically)
- ★ `perms_card` — **`(perms n).length = fact n`** (the Leibniz index set has
  `n!` members), via the bridge to `Combinatorics.Permutations.perms_length`
- ★★ `leibDet_card` — **the Leibniz determinant is a sum of exactly `n!` signed
  diagonal products**.

## Current Precision Results (0 free parameters)
Unchanged (pure combinatorics / linear algebra; no physics observable touched).

## Open Problems (Priority Order)
### 1. Abstract the COUNT duality meta-theorem
"Every finite duality = `sumOver_swap` on a 0/1 incidence + a SEPARATE cap per
axis" is witnessed (Sperner, Mirsky, Dilworth, LYM, Bollobás) but not abstracted
into one Lean theorem quantifying over incidences and caps.

### 2. Transport `mem_perms_iff` / `perms_nodup` across the `PermBridge`
`permsOf_eq` makes the two enumerations the *same list*, but the Combinatorics
`LPerm`/`Nodup` (Pairwise-based) and the `PermClosure` `LPerm`/`Nodup`
(cnt-based) are still distinct relations.  A relation-level bridge would let the
determinant side reuse `mem_perms_iff` / `perms_append_mem` directly (currently
each side re-derives sound/complete/nodup).  Low priority — both sides are
already complete; this is pure dedup.

### 3. Determinant multiplicativity / transpose — the SIGN-THEORY campaign
`det (M·N) = det M · det N` and `det Mᵀ = det M` are the remaining capstones.
A `/deep-research` pass this session (Mathlib `signAux`/`det_transpose`/`det_mul`,
mathcomp, Isabelle, Conrad, Baker — sources in the prompt log / chat) established
the strategy:

- **Our `psign` over `List Nat` is the right (constructive) definition** =
  Mathlib's `signAux` route, and being list-based it **dodges the
  `Multiset`/`Finset` quotient** that makes Mathlib's `sign` carry `Quot.sound` —
  why our `psign` is already PURE.
- **We already own the generating fact** `psign_swap_adj`/`psign_swap_prefix`
  ("adjacent transposition flips parity ±1") — the bootstrap for everything.
- **Keystone = `psign_mul` (`psign(σ∘τ)=psign σ·psign τ`)**; then `psign_inv` is a
  one-liner (`psign σ·psign σ⁻¹ = psign id = 1` in {±1}).  `det Mᵀ = det M` =
  reindex `perms` by `invPerm` + `psign_inv` + `prodZ_lperm` (product reindex).
- **`det(M·N)`**: Mathlib's direct-Leibniz route needs `psign_mul`; the
  *alternating-form-uniqueness* route reaches it from `det_swapRows` +
  "permute-rows-by-σ scales det by `psign σ`" (which needs a swap-reachability
  induction: sorted⟹iota + directed inversion-decrease — ~150 lines, no infra yet).

**Foundations built this session**:
- `PermGroup.lean` (19/19 PURE) — the symmetric group on value-lists: `composeList`
  (`(σ∘τ) i = σ(τ i)`), `iota n` two-sided identity, associativity, and `invPerm`
  with **two-sided** inverse (`composeList_invPerm_right/left`, `σ∘σ⁻¹ = σ⁻¹∘σ = iota n`).
- `PermSign.lean` (4/4 PURE) — the position-swap action: `composeList_swapAt`
  (`σ∘swapAt k τ = swapAt k (σ∘τ)`), `psign_swapAt` (adjacent swap negates `psign`),
  `swapAt_mem_perms` (`perms` closed under swap).

- ★★★ `PermSign.psign_mul` (`psign(σ∘τ) = psign σ·psign τ`) — **CLOSED, ∅-axiom PURE**.
  The keystone.  Built the full bubble-sort engine: `inv_prefix_swap` (directed
  inversion-decrease), `descent_of_inv_pos` (descent existence), `Q_swap` (the
  swap-invariant `psign(σ∘τ)·psign τ`), `sorted_perm_eq_iota` (base), `perms_inj`
  (position-injectivity via `cnt_ge_two`), and the structural fuel-induction
  `psign_mul_aux` (no well-founded recursion).  (`Nat.succ_ne_zero`'s `propext` was
  sidestepped with `Nat.noConfusion` to keep it PURE.)

- ✓✓✓ `DetTranspose.det_transpose` (`det n Mᵀ = det n M`) — **CLOSED, ∅-axiom PURE** (marathon
  Phases 1–2).  The full classical Leibniz proof from scratch: `psign_inv` (sign of inverse,
  Phase 1) + `invPerm_invol`/`perms_closed_invPerm` (the sum-reindex, Phase 2a) +
  `prodDiag_transpose_eq` (the product-reindex `∏ Mᵀ(i,σᵢ) = ∏ M(j,σ⁻¹ⱼ)` via `prodZ_lperm`,
  Phase 2b) + `leibDet_transpose`/`det_transpose` (assembly via `leibDet_eq_det`, Phase 2c).
  `DetTranspose` 16/16 PURE.

**`det(M·N) = det M·det N`** (the last big determinant capstone) — `DetMul.lean`, in progress:
  - ✓ §1 `composeList_mem_perms` (perms is a group), §2 `perms_closed_rightMul` (right translation
    is a bijection), §3 ★★★ **`leibDet_rowPerm`** (`leibDet (rowPerm σ B) = psign σ · leibDet B` —
    "permuting rows by σ scales det by `psign σ`") — all CLOSED, PURE (`DetMul` 8/8).
  - **Remaining — the function-sum expansion** (the last piece): `det(AB) = Σ_σ psign σ ∏ᵢ Σₖ AᵢₖBₖσᵢ
    = Σ_{f:[n]→[n]} (∏ᵢ Aᵢfᵢ)·(Σ_σ psign σ ∏ᵢ B_{fᵢ}σᵢ) = Σ_{f:[n]→[n]} (∏ᵢ Aᵢfᵢ)·leibDet(rowPerm f B)`.
    Non-injective `f` ⟹ `rowPerm f B` has two equal rows ⟹ `leibDet = 0` (`leibDet_rows_eq_ne`);
    permutation `f` ⟹ `psign f · leibDet B` (★ `leibDet_rowPerm`, just built).  So
    `det(AB) = (Σ_{f∈perms} psign f ∏ᵢ Aᵢfᵢ)·leibDet B = leibDet A · leibDet B`.  Needs: (a) an
    enumeration of **all** functions `[n]→[n]` (length-`n` lists with entries `<n`, not just perms)
    + (b) the product-of-sums distributivity `∏ᵢ(Σₖ …) = Σ_f ∏ᵢ …`, then (c) split injective/non-
    injective.  This is the big remaining build (~120 lines); `leibDet_rowPerm` (the hard sign part)
    is already done.

### 3b. ✓ The **upper-triangular** determinant — CLOSED (this session)
`DetTriangular.det_upper_triangular` — `M i j = 0` for `j < i` ⟹ `det = Π Mᵢᵢ`,
the dual of `det_lower_triangular`, via **last-row** cofactor expansion
(`cofExpand_lastRow` over `Laplace.cofactor_row_i`).  5 new lemmas, all PURE
(`DetTriangular` now 13/13).

### 3c. ✓ **Elementary row operations + general row swap** — CLOSED (this session)
`DetRowOps.det_addRowMul` — adding a multiple of one row to a distinct row
(`rowᵢ ← rowᵢ + t·rowⱼ`, `i ≠ j`) leaves `det` unchanged (the Gaussian-elimination
workhorse).  `DetRowOps.det_swapRows` — an **arbitrary** row swap negates `det`
(the alternating property for *any* row pair, not just `Laplace.det_rowSwap`'s
adjacent case), via the "swap = three adds + one negation" factoring.  Both need
no new sign theory — pure consequences of the already-proven multilinearity
(`det_setRow_add`/`det_setRow_smul`) + equal-rows-vanish (`det_rows_eq_ne`).
`DetRowOps` 11/11 PURE.

## File Map
```
lean/E213/Lib/Math/Algebra/Linalg213/DetTriangular.lean  ← + det_upper_triangular (last-row), 13/13 PURE
lean/E213/Lib/Math/Algebra/Linalg213/DetRowOps.lean      ← NEW: row ops (add-multiple preserves, swap negates) det, 11/11 PURE
lean/E213/Lib/Math/Algebra/Linalg213/PermGroup.lean      ← NEW: symmetric group on value-lists (composeList, identity, assoc, two-sided invPerm), 19/19 PURE
lean/E213/Lib/Math/Algebra/Linalg213/PermSign.lean       ← NEW: ★★★ psign_mul (sign-multiplicativity) via bubble-sort, 30/30 PURE
lean/E213/Lib/Math/Algebra/Linalg213/DetTranspose.lean   ← NEW: ★★★ det Mᵀ = det M (transpose determinant), 16/16 PURE
lean/E213/Meta/Nat/NatRing213.lean                       ← + nat_succ_sub (§5)
lean/E213/Lib/Math/Combinatorics/SpernerChains.lean      ← succ_sub_clean → nat_succ_sub
lean/E213/Lib/Math/Algebra/Linalg213/PermBridge.lean     ← NEW: the two-perms bridge, 7/7 PURE
lean/E213/Lib/Math/Algebra/Linalg213.lean                ← aggregator + PermBridge import
lean/E213/Lib/Math/Algebra/Linalg213/INDEX.md            ← determinant cluster section added
STRICT_ZERO_AXIOM.md                                     ← PermBridge entry (7 PURE)
research-notes/frontiers/count_substrate_synthesis.md    ← both items marked CLOSED
```

## Notes for next session
- `Linalg213/INDEX.md` was very stale (listed 10 files, ~25 present); added the
  determinant cluster but a full INDEX/count refresh is still owed (org-audit).
- `STRICT_ZERO_AXIOM.md` PermClosure entry count (76) predates its §11–13
  (multilinearity/degeneracy) — a re-count is owed there too.
