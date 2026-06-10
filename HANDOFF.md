# Session Handoff — 2026-06-10

## Branch
`claude/p-adic-reciprocity-topics-qBPUW` — pushed, ahead of `origin/main`.
`origin/main` merged in this session (179 commits).  `cd lean && rm -rf
.lake/build && lake build` ✓ clean (full fresh build, 307/307).  All new
theorems strict ∅-axiom PURE (`tools/scan_axioms.py`).  Ready-to-merge audit
GREEN (0 layer violations, 0 sink leaks, 0 stale refs).

## What Was Done This Session

### 1. Primitive-root marathon COMPLETE — full Zolotarev closed (∅-axiom)
The classical route to Zolotarev's lemma, end-to-end PURE.  ★★★★★
`ZolotarevCycle.zolotarev_full` (47 PURE): for an odd prime `p` (`2m=p−1`,
`m≥1`), unit `1≤a<p`, `psign (mulPerm a p) = 1 ⟺ a` is a QR mod `p`.

- **brick 6** `ZolotarevReduction.lean` (4 PURE) — `nonqr_psign_neg` +
  `zolotarev_iff`: given one non-residue `a₀` with `psign(mulPerm a₀)=−1`,
  the character law (`legendre_mul` + `psign_mulPerm_hom`) forces every
  non-residue odd; reduces full Zolotarev to one odd witness.
- **brick 7** `ZolotarevCycle.lean` (47 PURE) — the odd witness.
  `psign_mulPerm_primitive`: a primitive root `g` has `psign(mulPerm g p)=−1`.
  `mulPerm g` (fixes `0`, a `(p−1)`-cycle) is conjugate to the standard
  rotation `cycS=[0,p−1,1,…,p−2]` via the discrete-log list `τ(i)=g^{p−1−i}%p`
  (`conj_eq`); `psign` as a class function gives `psign(mulPerm g)=psign(cycS)
  =(−1)^{p−2}=−1` (`psign_cycS`, the `asc` ascending-block inversion calculus).
  `cycS`/`τ ∈ perms p` (`sFun_inj`; discrete-log injectivity `pow_inj_mod` via
  `res_cancel`+`ord_dvd`+periodicity `pow_period`).  `primitive_not_qr`
  (`ord g = 2m ∤ m`).  `pow_split_eq` exposed in `MulOrder`.

(Bricks 0–5 — `MulOrder`, `Lcm213`, `OrderPow`, `CoprimeOrder`, `MaxOrder`,
`Valuation`/`QPart`/`ValuationAlg`, `EveryOrdDvdMax`, `PrimitiveRoot` — closed
in prior sessions; `exists_primitive_root` = `(ℤ/p)*` cyclic is the engine.)

### 2. Merged `origin/main` (179 commits)
Main independently closed Zolotarev via the **μ/Gauss symmetric-cross-count**
route (`ZolotarevMuBridge.zolotarev_mu`, no primitive root) plus the rank-law /
ℚ(√5)-morphism / CP-phase arcs.  Conflict resolution: renamed this branch's
`ModArith.ZolotarevConverse` → `ZolotarevReduction` (main has a distinct file
at that name); took main's parallel `PermMatrixDet`/`SetoidMul`; unioned the
`Linalg213`/frontier-INDEX import lists.  Two independent ∅-axiom proofs of
Zolotarev now coexist.

### 3. Marathon skills (process → promote → crossdomain → essay → audit)
- **process**: 1 sink-rule decouple (`Zolotarev.lean` docstring off the
  deleted converse frontier note).  0 leaks remain.
- **promote**: new chapter `theory/math/numbertheory/primitive_roots.md`
  (the multiplicative-order + primitive-root + classical-Zolotarev sub-tree);
  cross-referenced from `zolotarev.md`; logged (promotion_essay_log row 46).
- **crossdomain**: `frontiers/zolotarev_crossdomain.md` addendum (insights
  5–6): `α(p)` is a multiplicative order (`ordModP` its rational shadow);
  `(5/p)` is the parity of `dlog_g(5)`.
- **essay**: `theory/essays/synthesis/the_quadratic_character_is_a_discrete_log_parity.md`
  — why `(a/p)` exists, via `(ℤ/p)*` cyclic of even order (row 47).
- **org-audit / purity / ready-to-merge**: all GREEN.

## Current Precision Results (0 free parameters)
No physics constants added this session (pure number theory; primacy = breadth
of ∅-axiom derivation, `seed/AXIOM/07_primacy.md` §7.1).  The physics precision
+ falsifier tables are current in `catalogs/physics-constants.md` /
`catalogs/falsifiers.md` (F1–F26, 100% paired).

## Open Problems (Priority Order)

### 1. Dedup: `Zolotarev.lean` (`mulPerm`) ↔ main's `ZolotarevSign.lean` (`mulPermMod`)
Byte-identical permutation definitions with parallel hom/QR lemmas — two
encodings of one object from parallel branches.  A clean merge needs:
exporting `res_cancel` (private as `res_cancel_le` in main), a `(a·b)` vs
`(a·b)%p` hom-form bridge lemma, and a `length_map_pure` replacement.  Its own
commit chain post-merge; both build PURE so not a blocker.
Frontier note: `research-notes/frontiers/zolotarev_crossdomain.md`.

### 2. The discrete-log readout `(a/p) = (−1)^{dlog_g(a)}` as a Lean theorem
The ripest buildable edge: ties `exists_primitive_root` to the standing
`psign`/Euler readouts, making "the character is a discrete-log parity" a
theorem not a reading.
Frontier note: `research-notes/frontiers/zolotarev_crossdomain.md` (insight 6).

### 3. `α(p)` as `ordModP`-in-`𝔽_{p²}` (rank law ↔ multiplicative order)
Run the `ord_dvd` Euclidean-split argument in `FP2SqrtD` to state the rank of
apparition as an order, unifying `ord_dvd_p_sub_one` (this branch) with
`rank_law_dispatch` (main).
Frontier note: `research-notes/frontiers/zolotarev_crossdomain.md` (insight 5).

## Unresolved from This Session
None attempted-and-failed.  The marathon closed fully; the open items above
are forward directions, not dead ends.  Note: `omega`, `Int.mul_one`,
`Nat.zero_mod`, `Nat.add_left_cancel`, `Nat.sub_eq_zero_of_le`,
`Nat.succ_ne_zero`, `Nat.sub_add_eq`, `Nat.sub_pos_of_lt` all carry propext —
use the repo's pure replacements (`NatHelper`/`Int213` + the `*_pure`/`*213`
families); confirmed throughout brick 6–7.

## Next
Either (a) the discrete-log readout theorem (Open Problem 2 — one Lean edge),
or (b) the `Zolotarev.lean`/`ZolotarevSign.lean` dedup (Open Problem 1).  Both
are well-scoped post-merge commit chains.

## Three-tier state
- **Promotions this session**: `theory/math/numbertheory/primitive_roots.md`
  ← the multiplicative-order / primitive-root / classical-Zolotarev sub-tree.
- **Promotion candidates**: none outstanding for this branch's work (all
  closed sub-trees have chapters).
- **Active scratchpad**: `frontiers/zolotarev_crossdomain.md` (insights 5–6 +
  dedup target).

## File Map
```
lean/E213/Lib/Math/NumberTheory/ModArith/ZolotarevCycle.lean      ← brick 7, full Zolotarev (47 PURE, new)
lean/E213/Lib/Math/NumberTheory/ModArith/ZolotarevReduction.lean  ← brick 6, the reduction (4 PURE, renamed from ZolotarevConverse)
lean/E213/Lib/Math/NumberTheory/ModArith/MulOrder.lean            ← pow_split_eq made public
lean/E213/Lib/Math/NumberTheory/ModArith/Zolotarev.lean           ← docstring decouple (homomorphism half; dedup target vs ZolotarevSign)
lean/E213/Lib/Math/NumberTheory/ModArith.lean                     ← umbrella (ZolotarevReduction + ZolotarevCycle wired)
theory/math/numbertheory/primitive_roots.md                       ← new chapter (promotion)
theory/math/numbertheory/zolotarev.md                             ← cross-ref to the generator route
theory/essays/synthesis/the_quadratic_character_is_a_discrete_log_parity.md  ← new essay
research-notes/frontiers/zolotarev_crossdomain.md                 ← addendum (insights 5–6, dedup target)
theory/{INDEX,math/INDEX,essays/INDEX}.md                         ← counts + listings (math 97, essays 78)
research-notes/promotion_essay_log.md                             ← rows 46 (promote) + 47 (essay)
```
