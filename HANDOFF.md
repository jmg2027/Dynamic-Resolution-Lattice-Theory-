# Session Handoff — 2026-06-08

## Branch
`claude/leibniz-determinant-perms-5zT6T` — `origin/main` merged in (Ollivier–Ricci
trichotomy, transcendentals/PDE ladders, chain/antichain duality, quadratic
reciprocity all present alongside the determinant work).  **READY TO MERGE** into
`main`: `rm -rf .lake/build && lake build` ✓ clean (forced fresh), `layer_audit`
0 violations, `kernel_regress` 45/45 0-axiom, 0 sorry/axiom/native_decide/Mathlib,
the determinant stack 137 theorems 0 dirty.

## What Was Done This Session (2026-06-08) — the DETERMINANT chapter CLOSED

The two sign-theory capstones are now both ∅-axiom PURE from scratch, on the
`PermSign.psign_mul` keystone:

- ★★★ **`DetTranspose.det_transpose`** — `det n Mᵀ = det n M` (16/16 PURE).
- ★★★ **`DetMul.det_matMul`** — `det n (A·B) = det n A · det n B` (**39/39 PURE**).

`DetMul` completes the Cauchy–Binet route: the diagonal product of `A·B`
distributes into a sum over the `n^n` index functions `funcs n`
(`prodDiag_matMul_expand` + `sumZ_swap` ⟹ `leibDet_matMul_expand`); the
**permutation** functions assemble to `leibDet A · leibDet B`
(`leibDet_rowPerm` + `psign_mul`, in `leibDet_perms_assembly`); the
**non-permutation** functions vanish by a *constructive* pigeonhole
(`firstDup` scans for a repeated value via the **pure `cnt`-decision** — the
default `Decidable (a ∈ l)` instance carries `propext`/`Quot.sound`, so it is
avoided everywhere; `nodup_imp_perm` + `term_zero_of_nonperm`).  The
funcs↔perms partition (`funcs_filter_perms_lperm`, again a `cnt`-based predicate)
glues the two halves.

Supporting determinant work this campaign (all PURE): `PermGroup` (19, symmetric
group on value-lists), `PermSign` (30, `psign_mul` via bubble-sort), `PermBridge`
(7, the two-perms bridge + `leibDet_card` = sum of `n!` terms), `DetTriangular`
(15, upper+lower), `DetRowOps` (11, row ops + general swap), `Meta/Nat`
`nat_succ_sub`.

Catalog (`STRICT_ZERO_AXIOM.md`) + `Linalg213/INDEX.md` updated.  Narrative:
`theory/essays/algebra/permutation_sign_as_homomorphism.md` (the sign as the
homomorphism both capstones descend from) written, settling the live fork in the
companion `determinant_as_quotient_characteristic.md`.  Synthesis seeds in
`research-notes/frontiers/determinant_closure_synthesis.md`.

## Current Precision Results (0 free parameters)
Unchanged — all work this campaign was pure mathematics (linear algebra,
permutation sign theory); no physics observable touched.  Physics constants +
falsifiers: `catalogs/physics-constants.md`.

## Open Problems (Priority Order)

### 1. Smooth general-`n` Perelman 𝓦-monotonicity (A6 smooth core)
The conformal frame reaches only the 2D case; smooth general-dimension Ricci
flow needs Riemannian tensor calculus + PDE a-priori estimates (none in
`lean/E213/`, Mathlib forbidden).  The genuine open edge of A6.
Frontier: `research-notes/frontiers/a6_ricci_core/ricci_flow_smooth_core.md`.

### 2. exp(a+b)=exp(a)·exp(b) at the series level + sin²+cos²=1 (T5)
Reachable: combine `binom2_theorem` + `choose_mul_factorials` into the cut-level
Taylor Cauchy convolution `(Σaʲ/j!)(Σbᵏ/k!)=Σ(a+b)ⁿ/n!` at the `Real213` level.
Frontier: `research-notes/frontiers/transcendentals/transcendental_functions_ladder.md`.

### 3. T4 cut-level `sqrtCut`
`Real213` `CauchyCutSeq` of `dyadicSqrtSeq a k / 2ᵏ` + `(sqrtCut a)²=a` up to
`cutEq` + `d/dx sqrt`.  Same frontier note.

### 4. P4 Li–Yau / Shi (discrete-PDE depth)
The "real analytic depth" of the PDE ladder — may stall.
Frontier: `research-notes/frontiers/pde_estimates/discrete_pde_estimates_ladder.md`.

### 5. Further Ollivier refinements
Bochner / CD(K,N) Bakry–Émery; concrete `κ` on more graphs.
Frontier: `research-notes/frontiers/a6_ricci_core/discrete_ricci_flow_ladder.md`.

### 6. Transport `mem_perms_iff` / `perms_nodup` across the `PermBridge`
`permsOf_eq` makes the two enumerations the same list, but the Combinatorics
`LPerm`/`Nodup` (Pairwise) and `PermClosure` `LPerm`/`Nodup` (cnt) are still
distinct relations.  Low priority — both sides complete; pure dedup.
Frontier note: `research-notes/frontiers/determinant_closure_synthesis.md`.

## Three-tier state
- **Promotions this session**: `theory/essays/algebra/permutation_sign_as_homomorphism.md`
  ← the closed sign theory (essay-side narrative for the determinant capstones);
  essay log row 16.
- **Promotion candidates**: a path-mirror chapter `theory/math/algebra/linalg213.md`
  fully covering the determinant stack could supplement the three algebra essays
  (sign / quotient-characteristic / Cayley–Hamilton); not blocking.  Transcendentals
  + PDE ladders remain open (T4/T5, P4); narrative deferred until they close.
- **Active scratchpad**: `research-notes/frontiers/{a6_ricci_core,transcendentals,
  pde_estimates}/`; `determinant_closure_synthesis.md` (next-campaign seeds).

## Next
Pick up the determinant-closure seeds (`det(permMatrix σ) = psign σ`; general column
Laplace expansion as a `det_transpose` corollary; relocate the constructive
pigeonhole to `Meta`) — see `research-notes/frontiers/determinant_closure_synthesis.md`;
or Open Problem #2 (exp(a+b) series convolution, the most reachable transcendentals
rung); or harvest a new domain (primacy = breadth).

## Notes for next session
- `STRICT_ZERO_AXIOM.md` PermClosure entry count predates its §11–13
  (multilinearity/degeneracy) — a re-count is owed.
- `Real213/ExpLog/` (17-file flat dir) flagged for a clustering pass (org-audit).

## File Map (this session)
```
lean/E213/Lib/Math/Algebra/Linalg213/DetMul.lean         ← det(A·B)=det A·det B completed, 39/39 PURE (cnt-pigeonhole; cnt_filter_le generalized)
lean/E213/Lib/Math/Algebra/Linalg213/DetTranspose.lean   ← header → current-state prose
lean/E213/Lib/Math/Algebra/Linalg213/PermClosure.lean    ← header → current-state prose
lean/E213/Lib/Math/Algebra/Linalg213/Permutation.lean    ← §5 doc → current-state ref
lean/E213/Lib/Math/Algebra/Linalg213/INDEX.md            ← DetMul line: det(M·N) done
STRICT_ZERO_AXIOM.md                                     ← DetMul entry 8→39 PURE (full det_matMul writeup)
theory/essays/algebra/permutation_sign_as_homomorphism.md ← NEW essay (the sign homomorphism)
theory/essays/algebra/determinant_as_quotient_characteristic.md ← open-fork settled
theory/essays/INDEX.md                                   ← essay 64→65 + new row
research-notes/frontiers/determinant_closure_synthesis.md ← NEW synthesis note (patterns + seeds)
research-notes/frontiers/count_substrate_synthesis.md    ← Leibniz-determinant seed CLOSED
research-notes/frontiers/INDEX.md                        ← determinant seed closure + new note registered
research-notes/promotion_essay_log.md                    ← row 16 (sign-homomorphism essay)
```
