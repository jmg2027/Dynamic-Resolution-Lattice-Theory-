# Session Handoff — 2026-05-13

## Branch
`claude/zero-axiom-work-P9NPI` — pushed, up to date with origin.
Latest: `0aaa6954 ModNat: delete unused funext-based gcd_upper_bound`.

## What Was Done This Session (cumulative 9 commits)

Marathon: **96 + ~50 = ~146 cumulative real DIRTY → PURE wins**.
Many DIRTY modules now fully PURE or downgraded from
`[propext, Quot.sound]` to `[Quot.sound]` only (funext-by-design
Cat 1 inherent).

### Track 1: ModArith cluster (+9 PURE) — commit c056a7dc

New helpers in `AddMod213`: `mod_self`, `add_mod_left_pure`,
`dvd_of_mod_eq_zero`, `mod_diff_eq_zero_of_le`.  New `Nat213.cases_lt_six`.

PURE conversions:
- `Lens.Leaves.ModNat.refines_implies_divides`
- `Lib.Math.ModArith.LensCRT.prod_refines_L6` (CRT 36-case enum)
- `Lib.Math.ModArith.JoinCoprime.{step_plus_k, mod_2_3_refines_const}` (+2)
- `Lib.Math.ModArith.JoinExample.{mod_4_6_chain_example, mod_4_6_step_two,
  mod_4_6_step_2k, mod_4_6_refines_parity}` (+4)

### Track 2: Int cluster (+5 PURE) — commits 50852bdb, 3397c867

PURE conversions:
- `Theory.Internal.treeTower_signed` (push_cast/omega → Int213
  sub_add_cancel_int + subNatNat_of_le)
- `Infinity.signedLens_image_ge_neg_one` (Int.toNat_of_nonneg → ctor split)
- `Infinity.signedLens_unbounded_above` (Int.le_refl → Int.NonNeg.mk)
- `DyadicTrajectory.alwaysTrue_le_alwaysFalse_at_limit`
  (Nat.mul_sub_left_distrib → Nat213.mul_sub)
- `DyadicTrajectory.alwaysTrueUnit_limit_eq_zero_at_pos_m`
  (omega → Nat.le_trans chain)

### Track 3: LeibnizAlgLift family (+5 PURE) — commit c88b1c78

New `Lib/Math/Cohomology/CupAW/PointwiseBilinear.lean` with 4 PURE
helpers (`delta_cupAW_add_right/left`, `cupAW_delta_add_right/left`).

15 new PURE per-index helpers: `V5_2Decomp.decomp_step_at_0..9` and
`V5_1DecompR.decomp_step_at_0..4` (avoiding the propext leak from
`simp only [decomp_5_*, bz5_*, Cochain.add]` via `show xor X false = X`
defeq trick + `cases (β k) <;> rfl`).

PURE conversions (5 LeibnizAlgLift variants):
- `LeibnizAlgLift.leibniz_via_β_decomp_lens`
- `LeibnizAlgLift22.leibniz_via_β_decomp_22`
- `LeibnizAlgLift21.leibniz_via_β_decomp_21`
- `LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21`
- `LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22`

### Track 4: LeibnizMid + Leibniz4Mixed cascade (+6 PURE) — commit 310173ac

New `Prop41.pattern_eq_at`, `Prop42.pattern_eq_at` (PURE pointwise).

PURE conversions:
- `Prop41.dsq_zero_prop_4_1`, `Prop42.dsq_zero_prop_4_2`
- `LeibnizMid.leibniz_universal_4_1_1`
- `Leibniz4Mixed.leibniz_universal_4_1_2`
- `Leibniz4Mixed.leibniz_universal_4_2_2`
- `LeibnizScaling.leibniz_aw_universal_closed_cases` (cascade)

### Track 5: Dead-code cleanup + GenericFamily (+5 effective) — commit 156fb84b

Deleted unused funext theorems:
- `V5Decomp.decomp_5_1_eq`, `V5_1DecompR.decomp_5_1_eq`,
  `V5_2Decomp.decomp_5_2_eq`
- `Prop41.pattern_eq`, `Prop42.pattern_eq`

PURE downgrade:
- `Cauchy.GenericFamily.leavesModAllLens_view`: propext → Quot.sound only
  (via `AddMod213.add_mod_gen` in place of Lean-core `Nat.add_mod`)

### Track 6: Leibniz Final + Bridges (+12 PURE) — commit 09898688

Bridges → pointwise helpers (`bz5_*_false_at`, `bz5_*_true_at`).
Removed unused funext bridges (`bz5_*_false`, `bz5_*_true`,
`cupAW_zero_*_fn`, `delta_zero_fn`).

PURE conversions:
- `Leibniz21Final.{h_components_α, leibniz_α_basis, h_components_β,
  leibniz_universal_5_2_1}` ★★★★★
- `Leibniz22Final.{h_components_α, leibniz_α_basis, h_components_β,
  leibniz_universal_5_2_2}` ★★★★★

### Track 7: Misc cleanup (+5 effective) — commit 8ad4a45d

- `CartesianVsDisjoint.DisjointVsProduct.power_dichotomy` (+1):
  Nat.mul_pow → `by decide` (6^25 literal eval)
- `Cohomology.CupAW.BilinearFunc`: deleted 3 unused funext bridges
  (cupAW_add_*_eq, delta_add_eq); file now empty namespace
- `Surfaces.T2Minimal.CupPairing.cup_symm` propext → Quot.sound only
  (Int.mul_comm/add_comm → Int213.* PURE)
- Cleaned 5 LeibnizAlgLift* `open` statements

### Track 8: FiniteContainsInfinite (+7 PURE) — commit 4a9f6dfa

New `Nat213.mul_left_cancel_pos` PURE helper.

PURE conversions:
- `UniverseChain.FiniteContainsInfinite.replicate_injective`:
  omega → explicit mod-5 reasoning (AddMod213.add_mod_left +
  Nat213.mul_mod_right + add_right_cancel + mul_left_cancel_pos)
- `any_iter_fits_some_level`: match k, hk → `rcases cases_lt_five`
- Module net: 5/2 → 7/0 PURE.

### Track 9: ModNat cleanup — commit 0aaa6954

Deleted unused `ModNat.gcd_upper_bound` (Lean-core Nat.gcd propext).
ModNat: 8/1 → 8/0 DIRTY.  `gcd213_upper_bound` (PURE) remains canonical.

## Reusable Patterns Established (cumulative this session)

| Pattern | Replacement |
|---|---|
| `funext + match j with ⟨k, _⟩ => ...` over indexed decomp | Per-index `decomp_step_at_k` PURE helpers (10 each for V5_2Decomp, V5_1DecompR) |
| `rw [function_eq]` (funext-based) | Pointwise lift via `cupAW_pointwise_eq` + `delta_pointwise_eq` |
| `simp only [decomp_5_*, bz5_*, Cochain.add]` (propext-leaking) | `show xor X false = X` (defeq) + `cases (β k) <;> rfl` |
| `Nat.mul_pow` (propext) | `by decide` on literal-Nat goals |
| `Nat.add_mod` (propext) | `AddMod213.add_mod_gen` (PURE) |
| `Int.mul_comm`/`add_comm` (propext) | `Int213.mul_comm`/`add_comm` (PURE) |
| `Nat.mul_sub_left_distrib` (propext via simp) | `Nat213.mul_sub` (PURE) |
| `omega` for impossible-Nat absurdity | `exfalso; exact absurd hn (by decide)` |
| `omega` for k≥2 from k+1≥2 + k≠1 | `Nat.lt_of_le_of_ne (Nat.le_of_succ_le_succ hn)` |
| Polynomial mul cancellation `5*a = 5*b → a = b` | `Nat213.mul_left_cancel_pos` (NEW PURE) |

## Current Precision Results (0 free parameters)

No precision results were added or modified this session.
See prior HANDOFF for the full table.

## Remaining DIRTY Categories (by-design Cat 1 inherent)

### Cat 1 inherent — funext / Quot.sound / propext via Prop-typed Lens

- `Lens.SemanticAtom.*` (~23) — Bool↔Prop bridge content
- `Lens.Universal.QuotLens.*` (5) — universalLens construction
- `Lens.Lattice.{Join, IndexedJoin, FamilyJoin}.*` — universalLens cascade
- `Lens.Algebra.Corresp.*` — Raw → Prop kernel correspondence
- `Lens.Properties.{TowerLevel3, CanonicalForm}.*` — universalLens-based
- `Lens.Compose.OnLens.*` (9) — Lens.combine_sym funext field
- `Lens.Compose.OnLensImage*` — funext on Cochain combine

### Cat 4 — heavy ring polynomial (omega + `hurwitz_ring` tactic)

- `CayleyDickson.{CayleyHeavy, SedenionHeavy, TrigintaduoionionHeavy}` (~10)
- `CayleyDickson.ZOmegaDomain` (5)
- `CayleyDickson.CDTower` (1, cascades)

### Cat 7 — Lean.Elab plumbing (Classical.choice inherent)

- `Meta.Tactic.{NativeGuard, DeriveConjugationCodomain, VerifyConjugation}.*`
- `Lib.Math.Tactic.QuadExtension` (elabQuadExtension)

### Cat 5 — Choice canonical (propext bridge by definition)

- `Lib.Math.Choice.CanonicalTruthChar.*` (~8)

### Cat 6 — Real-track Cauchy seq omega-heavy

- `Cauchy.WallisSharper.wallis_sharper_lower` (omega + poly_ineq)

## Next Experiment / Open Problems

### 1. WallisSharper.wallis_sharper_lower
Refactor possible but `poly_ineq` (private) uses many omegas across
polynomial identities + `Nat.mul_mul_mul_comm`.  Would need PURE
polynomial-identity helpers in Nat213.  Estimated 30-50 lines.

### 2. DRLT Validation Standard closure
Precision theorem AND falsifier for the same observable — explicit
closure (per CLAUDE.md "DRLT Validation Standard").  No closure
attempted this session.

### 3. Cat 1 inherent items — DESIGN-LEVEL refactor
The `Lens.Universal.QuotLens` and its dependents (~25+ DIRTY) would
require a fundamentally different Lens architecture (avoiding
`Raw → Prop` codomains and `Quot.mk`).  Out of scope for marathon.

### 4. Cat 4 heavy rings
The `hurwitz_ring` tactic produces large polynomial identity proofs.
Refactoring would require a custom PURE polynomial-normalisation
tactic.  Out of scope for marathon.

## File Map (this session)

| Commit | Key files |
|---|---|
| c056a7dc | AddMod213.lean, Nat213.lean, ModNat.lean, LensCRT.lean, JoinCoprime.lean, JoinExample.lean |
| 50852bdb | LensCardinality.lean |
| 3397c867 | DyadicTrajectory.lean |
| c88b1c78 | PointwiseBilinear.lean (NEW), V5_2Decomp.lean, V5_1DecompR.lean, 5× LeibnizAlgLift*.lean |
| 310173ac | Prop41.lean, Prop42.lean, LeibnizMid.lean, Leibniz4Mixed.lean |
| 156fb84b | GenericFamily.lean, V5Decomp.lean, V5_1DecompR.lean, V5_2Decomp.lean, Prop41.lean, Prop42.lean |
| 09898688 | 4× Leibniz Final/Bridge files |
| 8ad4a45d | DisjointVsProduct.lean, BilinearFunc.lean, CupPairing.lean, 5× LeibnizAlgLift*.lean |
| 4a9f6dfa | FiniteContainsInfinite.lean, Nat213.lean |
| 0aaa6954 | ModNat.lean |

## Cumulative Marathon State

- Before this session: 96 cumulative real DIRTY → PURE
- This session: ~50 (across 10 commits)
- **Total marathon: ~146 PURE wins**

## Key Anchor Documents

- `seed/CLOSED_FORM_SPEC.md` — Tier 5 propext-avoidance pattern catalog
- `STRICT_ZERO_AXIOM.md` — repo-wide PURE/DIRTY catalog (may be stale)
- `CLAUDE.md` — boot sequence + ∅-axiom standard
- `lean/E213/Lib/Math/Cohomology/CupAW/PointwiseBilinear.lean` — NEW
  value-level PointwiseBilinear infrastructure (Track 3)
- `lean/E213/Lib/Math/Cohomology/Cochain/V5_2Decomp.lean` — per-index
  PURE `decomp_step_at_0..9` helpers (Track 3)

Next session: run boot sequence (CLAUDE.md §1-4).  Remaining DIRTY is
mostly Cat 1 inherent (universalLens/Quot.sound) or Cat 4
(hurwitz_ring); largest tractable target is WallisSharper if a PURE
polynomial-identity tactic is built.
