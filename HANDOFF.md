# Session Handoff — 2026-06-08 (p-adic mul/diagLimit + det(permMatrix); merge marathon)

## Branch
`claude/p-adic-mult-det-2t7no` — `origin/main` merged in (the Legendre-symbol / QR
chapter promotion).  8 commits ahead of `origin/main`, pushed to
`origin/claude/p-adic-mult-det-2t7no` through the Task work (the merge-marathon
commits push at session end → merge to main).  `lake build` ✓ clean (full lib),
`layer_audit` 0 violations / 1553 Lib files, `kernel_regress` 45/45 0-axiom,
purity 0 sorry/axiom/native_decide/Classical/Mathlib.  **READY TO MERGE → main.**

## What Was Done This Session

Three open frontier seeds closed (the user's "곱셈 ZpSeqEquiv 항등식, det(permMatrix)=psign,
p-adic diagLimit"), then a full merge marathon (merge main → /process → promote →
cross-domain insights → /essay → /org-audit → /purity-check → /ready-to-merge → /handoff).

### 1. Multiplicative `ZpSeqEquiv` identities — `Padic/SetoidMul.lean` (7 PURE)
The multiplicative twin of `SetoidAssoc`'s additive-group capstone.  Lifts the
truncation-level ring-quotient theorems (`Zp.mul_trunc_comm`/`mul_trunc_assoc`/
`mul_add_trunc`/`add_mul_trunc`/`mul_trunc_one_left`) through `ZpSeqEquiv.of_trunc_all`:
`zp_mul_comm_equiv`/`zp_mul_assoc_equiv`/`zp_mul_one_left_equiv` (commutative monoid),
left+right distributivity, and `zp_setoid_commRing_capstone` — **`(ZpSeq p, ZpSeqEquiv)`
is a commutative ring**, funext/propext-free.

### 2. `det(permMatrix σ) = psign σ` — `Linalg213/PermMatrixDet.lean` (11 PURE)
The two readings of a permutation agree.  `permMatrix σ i j = [σ i = j]`; the Leibniz
sum `Σ_τ psign τ · Πᵢ[σ i = τ i]` collapses to the surviving `τ = σ` term:
`prodDiag_permMatrix_one/zero/self` (the diagonal product is 1 at `τ=σ`, 0 at the first
mismatch via `getD_ne_of_ne`), `sumZ_select` (nodup-list selector — `perms n` lists `σ`
once), `leibDet_permMatrix` → `det_permMatrix` (via `Laplace.leibDet_eq_det`),
`det_permMatrix_iota` (identity sanity).

### 3. Shared `Zp.diagLimit` abstraction — `Padic/Foundation.lean` (+rewire)
`invFull`/`sqrtFull`/`teichmuller` all built their target as the diagonal of a Cauchy
approximation sequence with an identical trunc-recursion.  Factored into
`Zp.diagLimit s := { digits := fun k => (s k).digits k }` + `diagLimit_trunc_succ`
(one proof from a one-step stability hypothesis).  All three defs rewired to
`Zp.diagLimit <seq>`; their `*_trunc_succ` lemmas collapse to one-liners feeding the
stability witness (`invSeq_succ_trunc_low`/`sqrtSeq_succ_trunc_low`/`teichmuller_iter_cauchy`).
Defeq-preserving — all downstream (Field/TeichmullerUnit/ZpSqrtD*) builds unchanged.

### 4. Merge marathon (docs / promotion / synthesis)
- Merged `origin/main` (Legendre-symbol/QR chapter).
- `/process`: 0 sink-rule violations, frontier-recording satisfied.
- Promotion (into already-promoted homes): `diagLimit` into `padic_real213.md`'s
  diagonal-extraction section, commRing Setoid into `pure_funext_avoidance.md`; log row 29.
- **Cross-domain frontier note** `frontiers/permutation_three_readouts.md`: four bridging
  edges between main's QR package and this branch (Zolotarev / Teichmüller μ_{p−1} /
  ring-quotient tower / Hensel-`diagLimit` √).
- **Essay** `theory/essays/synthesis/the_permutation_under_three_readouts.md` (log row 30).
- `/org-audit`: INDEX counts reconciled (theory math 92→94, essays 68→69; Padic INDEX
  +SetoidMul/diagLimit).

## Current Precision Results (0 free parameters)
**No physics-constant changes** (pure mathematics / foundations).  See
`catalogs/physics-constants.md` for the standing DRLT table (α_em 0.09 ppb, etc.).

## Open Problems (Priority Order)

### 1. ★ Zolotarev edge — close "one permutation, three readouts"
Prove `psign (×a mod p) = (a/p)` (Legendre symbol).  `det_permMatrix` already gives the
sign↔determinant edge; this third edge (`gauss_qr`/`euler_criterion` on the count side)
makes the triangle a theorem: `det(permMatrix(×a)) = (a/p)`.  Approach: define the value
list of `×a mod p`, show it ∈ `perms (p−1)` on units, pair inversion count with Gauss's `μ`.
Frontier note: `research-notes/frontiers/permutation_three_readouts.md` (insight 1).

### 2. p-adic Teichmüller ↔ quadratic character
State `qr_iff_pow_one` as a `μ_{p−1}`-component identity on `ω` (`(a/p)` = 2-torsion
projection of the Teichmüller unit), lifting QR p-adically.  Frontier note: same file,
insight 2.  Also `(a/p)=1 ⟺ a has a `diagLimit` √ in ℤ_p` (insight 4).

### 3. Carried-forward p-adic harvest seeds
`i₅ = teichmuller(2-lift)` concrete theorem (via `teichmuller_unique`); generalise the
lift+fixed-point uniqueness engine to `sqrt` (`unique_of_lift_fixed`).  Frontier:
`research-notes/frontiers/INDEX.md` "p-adic closure harvest".

### 4. Determinant / permutation-sign remaining seeds
General column Laplace as a `det_transpose` corollary; relocate the constructive
pigeonhole (`firstDup`/`mem_of_card_le`/`cnt_filter_le`) to `Meta`.  Frontier:
`research-notes/frontiers/INDEX.md` "determinant / permutation-sign".

## Unresolved from This Session
No dead ends.  One trap worth remembering: `rw [if_pos h]` / `if_neg h` need the proof
`h` to have the **exact** propositional form of the `if` condition — defeq is not enough
for `rw` to match the pattern.  Fix: ascribe the type first (`have hd : σ.getD i 0 = h :=
…`) so the `if`-condition is syntactically present, then `rw [if_pos hd]`.

## Next
Highest-value: **(1)** the Zolotarev edge — a single ∅-axiom lemma that turns the
cross-domain "one permutation, three readouts" picture into a theorem and binds this
branch's determinant stack to main's QR package.  Then **(2)** the p-adic lift of the
quadratic character.  Both seeded in `frontiers/permutation_three_readouts.md`.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: `diagLimit` → `padic_real213.md` (diagonal section);
  commRing Setoid → `pure_funext_avoidance.md`; essay
  `theory/essays/synthesis/the_permutation_under_three_readouts.md` (logged rows 29–30).
- **Promotion candidates**: none new closed-but-unmirrored (det/permutation + p-adic both
  already have chapters; this session augmented them).
- **Active scratchpad**: `research-notes/frontiers/permutation_three_readouts.md` (the four
  cross-domain edges) + the standing p-adic / determinant seeds in `frontiers/INDEX.md`.

## File Map
```
lean/E213/Lib/Math/NumberSystems/Padic/SetoidMul.lean        ← NEW (7 PURE) mul Setoid identities + commRing capstone
lean/E213/Lib/Math/Algebra/Linalg213/PermMatrixDet.lean      ← NEW (11 PURE) det(permMatrix σ) = psign σ
lean/E213/Lib/Math/NumberSystems/Padic/Foundation.lean       ← +diagLimit + diagLimit_trunc_succ
lean/E213/Lib/Math/NumberSystems/Padic/Hensel.lean           ← invFull/sqrtFull rewired to diagLimit
lean/E213/Lib/Math/NumberSystems/Padic/Teichmuller.lean      ← teichmuller rewired to diagLimit
lean/E213/Lib/Math/Algebra/Linalg213.lean                    ← +PermMatrixDet import
lean/E213/Lib/Math/Algebra/Linalg213/INDEX.md                ← +PermMatrixDet row
lean/E213/Lib/Math/NumberSystems/Padic/INDEX.md              ← +SetoidMul row, Foundation +diagLimit, dep tree
theory/math/numbersystems/padic_real213.md                   ← diagLimit named in diagonal section + key-results row
theory/essays/methodology/pure_funext_avoidance.md           ← +commutative-ring Setoid closure
theory/essays/synthesis/the_permutation_under_three_readouts.md  ← NEW essay
theory/essays/INDEX.md, theory/INDEX.md                       ← essay registered + counts (math 94, essays 69)
research-notes/frontiers/permutation_three_readouts.md        ← NEW cross-domain frontier (4 edges)
research-notes/frontiers/INDEX.md                             ← seeds marked done + new note registered
research-notes/promotion_essay_log.md                         ← rows 29 (promotion) + 30 (essay)
```
