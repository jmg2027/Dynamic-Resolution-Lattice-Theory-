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

### 3. Determinant multiplicativity / transpose
`det (M·N) = det M · det N` and `det Mᵀ = det M` are the natural next capstones
on the now-complete Leibniz/Laplace stack (adjugate identity already in hand).
**Caveat (scouted this session)**: both need a substantial new sign-theory
lemma — `det Mᵀ = det M` needs inversions-of-inverse (`inv σ⁻¹ = inv σ`) or
sign-multiplicativity `psign(σ∘τ)=psign σ·psign τ`; `det(M·N)` needs the
function-enumeration expansion + multilinearity.  Neither is a quick close;
`ProdLperm` (`prodZ`/`prodZ_lperm`/`prodZ_append`) is the laid foundation for
the transpose reindex.

### 3b. ✓ The **upper-triangular** determinant — CLOSED (this session)
`DetTriangular.det_upper_triangular` — `M i j = 0` for `j < i` ⟹ `det = Π Mᵢᵢ`,
the dual of `det_lower_triangular`, via **last-row** cofactor expansion
(`cofExpand_lastRow` over `Laplace.cofactor_row_i`).  5 new lemmas, all PURE
(`DetTriangular` now 13/13).

### 3c. ✓ **Elementary row operations** — CLOSED (this session)
`DetRowOps.det_addRowMul` — adding a multiple of one row to a distinct row
(`rowᵢ ← rowᵢ + t·rowⱼ`, `i ≠ j`) leaves `det` unchanged (the Gaussian-elimination
workhorse).  No new sign theory — pure consequence of the already-proven
multilinearity (`det_setRow_add`/`det_setRow_smul`) + equal-rows-vanish
(`det_rows_eq_ne`).  `DetRowOps` 4/4 PURE.

## File Map
```
lean/E213/Lib/Math/Algebra/Linalg213/DetTriangular.lean  ← + det_upper_triangular (last-row), 13/13 PURE
lean/E213/Lib/Math/Algebra/Linalg213/DetRowOps.lean      ← NEW: rowᵢ += t·rowⱼ preserves det, 4/4 PURE
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
