# Session Handoff — 2026-06-08 (Zolotarev converse closed + merge marathon)

## Branch
`claude/converse-psign-character-ZEsQA` — pushed, **ahead of `origin/main`**
(merge marathon).  `cd lean && lake build E213` ✓ clean.  All new theorems strict
∅-axiom PURE (`tools/scan_axioms.py`).  **NOTE**: `origin/main` advanced during the
marathon — re-merge `origin/main` before the final push/merge.

## What Was Done This Session

**Zolotarev's lemma is fully closed for every odd prime, ∅-axiom PURE.**  The
sign of the multiply-by-`a` permutation IS the Legendre symbol:
`psign σ_a = 1 ⟺ a` is a QR (`ModArith/ZolotarevMuBridge.zolotarev_mu`).  This
closes the converse that began as "a separate multi-session effort" — no primitive
root needed.

### 1. Reusable permutation-sign combinatorics (`Linalg213/InversionsAppend.lean`, 28 PURE)
- `inversions_append` / `psign_append` — `L ++ M` sign via cross-term
  `crossInv L M = Σ_{x∈L} ltCount x M`.
- propext-free reversal `revL` (+ `map_snoc`, `revL_lperm`, `ltCount_revL`,
  `revL_getD`, `getD_append_left/right`, `length_append_pure`) — `List.reverse` /
  `map_append` / `mem_append` all pull `propext`, so a self-contained reversal is used.
- ★ `psign_csub_revL`: `psign ((revL L).map (c−·)) = psign L`.
- ★ `psign_blockForm`: `psign (0 :: L ++ (revL L).map (p−·)) = altSign (crossInv L …)`.
- ★ `altSign_crossInv_map_psub`: symmetric cross-count `= altSign (diagCount p F)`
  (off-diagonal pairs cancel mod 2; `psub_lt_symm`).

### 2. The full converse (`ModArith/ZolotarevMuBridge.lean`, 14 PURE)
- `neg_mul_mod`: `(a·(p−x)) % p = p − (a·x) % p`.
- `mulPermMod_block`: `σ_a = 0 :: (fhList ++ (revL fhList).map(p−·))` (since
  `σ_a(p−x) = p − σ_a(x)`).
- `psign_mulPermMod_eq_diag` → `altSign (diagCount p fh)`; `pm_lt`/`sgn_helper`/
  `altSign_diag_eq_prodSgn` → `= ∏ sgFn` (Gauss's `μ`).
- ★ `zolotarev_mu`: `psign σ_a = 1 ⟺ QR(a)`, all odd primes.
- ★ `det_permMatrix_mulPermMod`: `det (permMatrix σ_a) = (a/p)` — the "one
  permutation, three readouts" triangle (psign = det = Legendre) closed universally.

### 3. Earlier this branch (already pushed before the marathon)
- `ModArith/ZolotarevConverse.lean` (23 PURE): `p ≡ 3 (mod 4)` full identity +
  the `−1` corner `psign σ_{−1} = (−1)^m = (−1/p)` (universal) + det triangle (p≡3).

### 4. Merge marathon (skills)
- Merged `origin/main` (one-carrier / p-adic νF arc, Casoratian / spiral-axis,
  CKM CP-phase, finite-state-of-the-pointing); resolved the `ZolotarevSign` docstring
  conflict to the now-complete state.
- `/process`: 1 → 0 sink violations; `frontiers/INDEX.md` Zolotarev edges marked CLOSED.
- Promotion: `theory/math/numbertheory/zolotarev.md` (log row 38).
- Cross-domain: `frontiers/zolotarev_crossdomain.md` (4 bridges branch × main).
- `/essay`: `theory/essays/synthesis/the_legendre_symbol_is_the_sign_of_a_pointing.md`
  (log row 39).
- `/org-audit` + `/purity-check` + `/ready-to-merge`: all green.

## Current Precision Results (0 free parameters)
Unchanged this session — Zolotarev is pure-math closure, not a physics observable.
See `catalogs/physics-constants.md` (inherited from main: `1/α_em` 0.09 ppb, CKM
`δ = 90°`, `R_u = 1/φ²`, …).

## Open Problems (Priority Order)

### 1. The remaining "three readouts" faces (insights 2–4)
The Teichmüller `ω`-projection face of the quadratic character, the
`ZpSeq ↠ ℤ/pⁿ ↠ ℤ/p` truncation-tower reading, and the Hensel/`diagLimit`
square-root face (`(a/p)=1 ⟺ a has a √ in ℤ_p`).  Proven cores closed both sides;
the bridging edges are open.
Frontier note: `research-notes/frontiers/permutation_three_readouts.md` (insights 2–4).

### 2. Branch × main cross-domain bridges (ripe: insights 1–2)
(1) `(a/p)` as the Z/2 invariant the finite `×a` pointing carries that the `×p`
νF-escape lacks; (2) `psign (cyclicShift n) = altSign (n−1)` through `det_permMatrix`
(mirroring `psign σ_a = (a/p)`), unifying Zolotarev with main's Casoratian companion
sign as one "three readouts" family; (3) `crossInv` antisymmetry ↔ det repeated-row
vanishing; (4) `psign σ_{−1} = (−1/p)` ↔ main's order-4 spiral-axis point `ℤ[i]^×=C₄`.
Frontier note: `research-notes/frontiers/zolotarev_crossdomain.md`.

## Unresolved from This Session
None — the μ-bridge closed cleanly.  Self-corrected dead ends to NOT re-attempt:
`omega` / `Nat.sub_sub` / `Nat.add_sub_cancel_left` / `Nat.div_add_mod` /
`Nat.mod_two_eq_zero_or_one` / `Nat.sub_add_cancel` / `List.reverse_cons` /
`Nat.lt_of_mul_lt_mul_left` / `Nat.le_sub_of_add_le` — all pull `propext`/`Classical`
in this Lean core; use the repo's pure replacements (`NatHelper.*`, `AddMod213.*`,
`MulMod213.*`, self-defined `revL`/`sub_one_sub`).

## Next
Push and merge this branch to `main` (re-merge `origin/main` first — it advanced
during the marathon).  After merge: attack Open Problem 2 insight (2) — the buildable
`psign (cyclicShift n) = altSign (n−1)` edge tying Zolotarev to the Casoratian.

## Three-tier state
- **Promotions this session**: `theory/math/numbertheory/zolotarev.md` (row 38) +
  essay `the_legendre_symbol_is_the_sign_of_a_pointing.md` (row 39).
- **Promotion candidates**: none outstanding for the Zolotarev arc (closed + promoted).
- **Active scratchpad**: `frontiers/{permutation_three_readouts, zolotarev_crossdomain}.md`.

## File Map
```
lean/E213/Lib/Math/Algebra/Linalg213/InversionsAppend.lean   ← NEW, 28 PURE (reusable sign combinatorics)
lean/E213/Lib/Math/Algebra/Linalg213.lean                    ← +InversionsAppend import
lean/E213/Lib/Math/NumberTheory/ModArith/ZolotarevMuBridge.lean ← NEW, 14 PURE (full converse)
lean/E213/Lib/Math/NumberTheory/ModArith/ZolotarevConverse.lean ← p≡3 + −1 corner (23 PURE)
lean/E213/Lib/Math/NumberTheory/ModArith/ZolotarevSign.lean  ← docstring → fully-closed state
lean/E213/Lib/Math/NumberTheory/ModArith.lean                ← +ZolotarevConverse, +ZolotarevMuBridge
theory/math/numbertheory/zolotarev.md                        ← NEW promoted chapter
theory/essays/synthesis/the_legendre_symbol_is_the_sign_of_a_pointing.md ← NEW essay
research-notes/frontiers/permutation_three_readouts.md       ← Zolotarev edge marked CLOSED
research-notes/frontiers/zolotarev_crossdomain.md            ← NEW (branch × main, 4 bridges)
research-notes/frontiers/INDEX.md                            ← Zolotarev seeds → Done
research-notes/promotion_essay_log.md                        ← rows 38 (promotion) + 39 (essay)
theory/{INDEX,math/INDEX,essays/INDEX}.md                    ← counts: math 95, essays 74
```
