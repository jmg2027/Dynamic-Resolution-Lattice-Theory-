# STRICT ∅-AXIOM — the 213 axiom standard

> **Canonical definitions (single source of truth):** see "Terms"
> section below.  When other documents (HANDOFF.md, CLAUDE.md,
> scan_all_axioms.py comments) drift from these definitions, this
> file wins.  Falsifiability anchor: `seed/AXIOM/04_falsifiability.md` §5.2.1.

## Terms (canonical)

| Term | Definition |
|---|---|
| **PURE** | `#print axioms <thm>` returns "does not depend on any axioms".  Identical to "strict ∅-axiom".  This is the standard target. |
| **DIRTY** | `#print axioms` returns "depends on axioms: [...]" with a non-empty list.  Any of `propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` (from `native_decide`), `sorryAx`. |
| **sealed-DIRTY-by-design** | A DIRTY theorem accepted because (a) Lean-core boundary (well-founded recursion, Lean.Elab metaprogramming inheriting Classical.choice via the Lean.Elab.Command monad), or (b) Lens funext-by-design (higher-order Lens equality requires funext on the combine field, refactoring would redefine what "Lens equality" means).  Listed in `tools/scan_all_axioms.py` `SEALED_DIRTY_PREFIXES`. |
| **real DIRTY** | DIRTY ∧ NOT sealed-by-design.  This is the regression budget. |

**The 213 axiom set is ∅** — a theorem meets the standard iff PURE.

**Forbidden absolutely** (per `seed/AXIOM/04_falsifiability.md` §5.2.1, falsifiability
trigger): `Classical.choice` and `Lean.ofReduceBool` in **213
mathematical content** (theorems about Raw, Lens, observables).
Tactic files (`E213.Meta.Tactic.*`) that inherit Classical.choice
purely via the Lean.Elab.Command monad are *plumbing*, not 213-math
content; sealed under (a) above with explicit justification.

**Always allowed but not target**: `propext` and `Quot.sound` are
part of the Lean 4 core kernel base.  213 aims to avoid them where
possible (PURE target) but does not falsify if a result requires
them via Lean-core well-founded recursion proofs.

---

## Latest scan

(Numbers vary by run due to scanner timeouts on slow modules; refer
to HANDOFF.md "current state" for the freshest reading.  994 total
`.lean` files; scanner enumerates ~500-800 ★-marked theorems
depending on timeout state.)

**2026-05-09 (later, marathon batch 1)**: User directive "seal
없애버리고 다 213 native로" — emptied SEALED_DIRTY_PREFIXES.  Full
scan post-seal-empty: **2491 PURE / 164 DIRTY / 0 sealed**.

After batch 1-10 fixes (27 theorems converted): **2519 PURE / 137
DIRTY / 0 sealed**.

Marathon progress this session: **27/164 (16.5%)**.

**2026-05-10 (continuation, Lens equality refactor / G83 marathon)**:
Continuation of marathon under "Lens equality 재정의 strategy"
directive.  Phase 1 + Phase 2 complete with eqPW infrastructure:

Phase 1 — Infrastructure (`lean/E213/Lens/EqPW.lean`):
  - `Lens.eqPW L M` — pointwise Lens equality definition
  - `eqPW_refl`, `eqPW_symm`, `eqPW_trans` — equivalence
  - `eqPW_view_a`, `eqPW_view_b`, `eqPW_combine_sym_transfer`
  - `eqPW_view_of_sym` — view bridge under symmetric combine
  - `Lens.fold_slash_eqPW` — fold/slash compatibility for eqPW sym
  All ∅-axiom (PURE).

Phase 2 — Cat 1 conversions (11 PURE + 4 PURE companions + 2 partial):

PURE (was DIRTY):
  - SemanticAtom.isLensExpressible_iff_foldStructured  [Quot.sound] → ∅
  - SemanticAtom.raw_initial                          [Quot.sound] → ∅
  - Morphism.FoldStructured.fold_structured_lens_expressible      → ∅
  - Morphism.FoldStructured.lens_expressible_iff_fold_structured  → ∅
  - Lattice.IndexedJoin.iProdLens_view              [Quot.sound] → ∅
  - Lattice.IndexedJoin.iProdLens_refines_each      [Quot.sound] → ∅
  - Instances.Cauchy.pointwise_limit_match          [Quot.sound] → ∅
  - Characterisation.Core.R4_conj_unique_of_surjective [Quot.sound] → ∅
  - Compose.OnLens.lensUniversalMorphism            [Quot.sound] → ∅
  - Compose.OnLens.lensUniversalMorphism_a          [Quot.sound] → ∅
  - Compose.OnLens.lensUniversalMorphism_b          [Quot.sound] → ∅

NEW PURE eqPW companions (alongside existing DIRTY originals):
  - Compose.OnLens.lensXor_comm_eqPW
  - Compose.OnLens.lensCombineGeneric_comm_eqPW
  - Compose.OnLens.lensUniversalMorphism_slash_eqPW

Partial (Quot.sound removed but propext remains):
  - Leaves.Mod3.leavesMod3Lens_view_eq    [propext, Quot.sound] → [propext]
  - Leaves.Mod3.leaves_refines_mod3       [propext, Quot.sound] → [propext]
  - App.Simplex.block_constant_implies_aut_invariant
                                          [propext, Quot.sound] → [propext]

Patterns added to playbook:
9. Function-eq capstone (`f = g : Raw → α`) → pointwise (`∀ r, f r = g r`)
   to avoid funext.  Trivial change at the leaf, downstream consumers
   adjust.
10. Index-pointwise iProdLens — split on canonical-form cmp at the
    index level instead of going through function-level Raw.fold_slash.
11. eqPW companion pattern — for Cat 1 `L = M : Lens α` lemmas, add
    `(L).eqPW M` sibling without removing the DIRTY original; new
    consumers migrate gradually.

**Post-session scan (verified, final)**: **2654 PURE / 129 DIRTY** (2783 total).
(Mid-session checkpoint: 2644/133 — continuation batch +10 PURE, -4 DIRTY.)

DIRTY breakdown (cumulative session):
  - 54  [propext]                              (was 50 at session start)
  - 46  [propext, Quot.sound]                  (was 50)
  - 18  [Quot.sound]                           (was 33 — **−15** from Cat 1 work)
  - 9   [propext, Classical.choice, Quot.sound] (Lean.Elab plumbing)
  - 2   [propext, Quot.sound] (split format)

The `[Quot.sound]`-only category dropped 33 → 18 (−15, ~45% reduction) —
direct hit of the G83 Lens-equality refactor.

**Continuation batch**: more PURE wins via the eqPW-companion + typeclass-
bypass patterns:
  - `Compose.OnLens.universalMorphismLevelTwo`             [Quot.sound] → ∅
  - `Compose.OnLens.universalMorphismLevelThree`           [Quot.sound] → ∅
  - `Lens.Instances.FunctionSpace.funUniversalMorphism`    [Quot.sound] → ∅
  - `Lens.Instances.FunctionSpace.boolFunUniversal`        [Quot.sound] → ∅

New PURE eqPW companions (alongside DIRTY originals):
  - `EqPW.Lens.view_unique_eqPW`              (∅-axiom view-unique companion)
  - `OnLens.lensXor_eqPW_cong`                (eqPW-congruence of lensXor)
  - `OnLens.lensCombineGeneric_eqPW_cong`     (eqPW-congruence of generic)
  - `OnLensImage.lensUniversalMorphism_factors_eqPW`     (factor PURE)
  - `OnLensImage.lensUniversalMorphism_image_eqPW`       (image PURE)
  - `OnLensImageGeneric.lensUniversalMorphism_factors_generic_eqPW`
  - `Lattice.IndexedJoin.iProdLens_is_greatest_pw`        (per-index PURE)

DIRTY breakdown:
  - 54  [propext]                                     (was 50)
  - 46  [propext, Quot.sound]                         (was 50)
  - 22  [Quot.sound]                                  (was 33 — **Cat 1 hit**)
  - 9   [propext, Classical.choice, Quot.sound]       (was 9 — Lean.Elab plumbing)
  - 2   [propext, Quot.sound] (split format)          (was 2)

The `[Quot.sound]`-only column dropping 33 → 22 (-11) is the
direct Cat 1 conversion signal — those were genuine "Lens equality
via funext on combine" leaks, exactly the G83 target.

The remaining DIRTY split:
  - Inherent Prop-codomain (`Raw → Prop` from `universalLens`):
    [propext, Quot.sound] — universalLens / FamilyJoinEquiv / Lattice.Join
  - Inherent Lens-eq-on-Bool (Cat 1 with no eqPW migration yet):
    [Quot.sound] — lensBoolHasDistinguishing chain, Tower levels
  - Inherent simp-from-omega: [propext] — Mod3, Cauchy, etc.
  - Heavy ring polynomial: [propext, Quot.sound] — CayleyHeavy, Sedenion
  - Lean.Elab plumbing: [propext, Classical.choice, Quot.sound] —
    NativeGuard, DepthJoin (uses Classical.choice indirectly)

Patterns established (8 reusable):
1. omega → Nat.le_trans + Nat.le_add_right + Nat.add_le_add
2. cases h (impossible Nat eq) → absurd h (by decide)
3. injEq.mp .2 → congrArg <projector>
4. cmp_eq_iff.mp → cmp_eq_to_eq (existing direct lemma)
5. simp [...] → show <expanded> + rw [explicit lemma] / absurd
6. Iff lemma cascade → direct .mp/.mpr lemmas (cmp_gt_to_lt_swap etc.)
7. simp only [def, h] → show <unfolded match form>; rw [h]
8. inline 213-native max_comm via case-split (avoid Nat.max_comm propext)

Cascade fix found: Raw.swap_slash → Lens.Swap (5 fixes from 1 source).

After batch 1-5 fixes: 2507 PURE / 148 DIRTY.

Earlier batch 1 fixes (5 theorems):

Modules now PURE:
- E213.Lens.Properties.Leaf (was 2 dirty)
- E213.Lens.Diagonal (was 1 dirty)
- E213.Lib.Math.CayleyDickson.LipschitzLens (was 1 dirty)
- E213.Lens.Instances.RawAChar (was 1 dirty)
- E213.Lens.Instances.SumNotCoproduct (was 1 dirty)
- E213.Lens.Instances.SumNotCoproductGeneric (was 1 dirty)
- E213.Lens.Instances.CompoundBool (was 4 dirty)
- E213.Lens.Instances.Sum (was 3 dirty)
- E213.Lens.Properties.Characterisation.Core (was 3 dirty, now 1 — funext only)

Patterns established (5 reusable):
1. omega → Nat.le_trans + Nat.le_add_right + Nat.add_le_add
2. cases h (impossible Nat eq) → absurd h (by decide)
3. injEq.mp .2 → congrArg <projector>
4. cmp_eq_iff.mp → cmp_eq_to_eq (existing direct lemma)
5. simp [...] → show <expanded> + rw [explicit lemma] / absurd

Earlier batch 1 fixes (5 theorems converted): **2496 PURE / 159
DIRTY / 0 sealed**.  Patterns established:
- `omega` → `Nat.le_trans` + `Nat.le_add_right` + `Nat.add_le_add`
- `cases h` (impossible Nat eq) → `absurd h (by decide)`
- `injEq.mp` → `congrArg <projector>`
- `Tree.cmp_eq_iff.mp` → `Tree.cmp_eq_to_eq` (∅-axiom direct lemma)
- `simp [this]` (using Iff hypothesis) → `decide_eq_true` direct

Files now PURE (was DIRTY):
- E213.Lens.Properties.Leaf (was 2 dirty)
- E213.Lens.Diagonal (was 1 dirty)
- E213.Lib.Math.CayleyDickson.LipschitzLens (was 1 dirty)
- E213.Lens.Instances.RawAChar (was 1 dirty)

**Remaining marathon**: 159 items.  Categorization:
  62  [propext]                          — most tractable
  55  [propext, Quot.sound]              — Lens funext typically
  31  [Quot.sound]                       — funext usage
   9  [propext, Classical.choice, Quot.sound]  — Lean.Elab plumbing
   2  [propext, Quot.sound] (split format)

Top remaining DIRTY modules:
  25  E213.Lens.SemanticAtom (Prop-level "atom of meaning")
  14  E213.Lens.Compose.OnLens (Lens funext-by-design)
  10  E213.Lens.Instances.Leaves.DepthJoin (JoinEquiv on Raw + Classical)
  10  E213.Lens.Properties.Morphism.BoolProp
   6  Lens.Instances.Reach, Lens.Lattice.IndexedJoin, Lib.Math.
       CayleyDickson.CayleyHeavy

**Hard categories requiring structural refactor**:
- Lens equality redefinition (avoid funext): ~90 items
- Math.Infinity Iff/Cantor proofs: ~5 items
- Heavy ring polynomials (CayleyHeavy etc.): ~15 items
- Lean.Elab Tactic plumbing: 9 items

**2026-05-09** (post-Möbius-extension session, pre-merge audit):
seal list updated to use single-`Lens.*` prefixes (was `Lens.Lens.*`
— stale from earlier nesting).  Tree-wide scan after seal-list fix
reports **2491 PURE / 75 DIRTY + 89 sealed-DIRTY-by-design** (2655
total).  Real DIRTY breakdown: 32 [propext, Quot.sound] + 32
[propext] + 7 [propext, Classical.choice, Quot.sound] +
2 [Quot.sound] + 2 [propext, Quot.sound] (split format).

The 75 real DIRTY items are **pre-existing** from before the
Möbius-extension session.  All 102 ∅-axiom theorems newly added
in `Theory/Nat213/` + `Theory/Tower/` + `Lib/Math/UniverseChain/
MobiusChain.lean` are PURE.

Topical breakdown of remaining DIRTY:
- Lens.Leaves.DepthJoin (10): JoinEquiv-on-Raw uses Classical.choice
- Lens.Morphism.BoolProp (10): BoolProp morphisms via propext
- Lib.Math.CayleyDickson.CayleyHeavy (6): heavy ring polynomial
  identities via simp
- Lens.Universal.QuotLens (5): Lens funext-by-design
- Lib.Math.CayleyDickson.ZOmegaDomain (5): ring axioms via simp
- Lens.Instances.Swap, Sum, CompoundBool (3-4 each): Lens patterns
- Misc Lens + Math files (1-3 each): scattered residuals

These need separate marathons; many would seal under expanded
"Lens funext-by-design" or "heavy polynomial identity" categories,
but proper triage requires per-theorem inspection.

**2026-05-05** (post-AXIOM.md §9.1 rename audit pass): tree-wide
scan reports approximately **541 PURE / 18 DIRTY / 14 sealed-DIRTY-
by-design** (573 total counted).  Real DIRTY breakdown: 10 [propext]
+ 7 [propext, Quot.sound] + 1 [propext, Classical.choice, Quot.sound]
(NativeGuard internal; Classical.choice via Lean.Elab API, sealed
upstream).  Compared to pre-rename 2026-05-04 baseline (511/14/22),
the rename caused +30 PURE (newly counted), +4 DIRTY (newly counted
pre-existing items), -8 sealed (entries reclassified after seal-list
update for `Meta.SelfRecognising` + `DeriveConjugationCodomain` +
`VerifyConjugation`).  No new actual axiom dependencies were
introduced by the rename.

**Earlier session 27 milestone (2026-05-03)**: scan reported **2077
PURE / 0 real DIRTY / 19 sealed**.  The 2077 count reflected a more
permissive scanner regex catching additional ★-marked theorems
across the Real213 marathon.  Cumulative arc 394 → 0 real DIRTY
across sessions 19-27 via Plan 2 parallel-struct refactor PLUS
deletion of ALL function-eq facade + consumer migration to `_at`
pointwise form.

**Genuine final state** (no cheat seal):
  - The function-eq facade across Phase capstones, Flux*/FTC*
    capstones, ClassicCalc/Passthrough/HasDyadicMVTWitness struct
    families, and leaf cut lemmas (CutMulOne/SumZero/PowConst/MidSelf)
    has been **completely deleted**.  All ~25 consumer files
    migrated to use only `_at` pointwise variants.
  - Function-eq cut equality on `Nat → Nat → Bool` would require
    funext = Quot.sound — but it's no longer needed: every theorem
    is now stated and proved pointwise.
  - The 6 propext-bearing residuals (CubeDerivativeAtZero × 3,
    PolySumDerivativeModulus × 3) refactored using
    cutSumAux_congr / cutMulOuter_congr cascades + manual Nat
    arithmetic avoiding `omega`/`Nat.max_eq_left`.

**The 19 sealed items** are mathematically inherent (NOT facade):
  - Lean-core boundary: Nat.lcm/gcd/add_mod/Int from kernel use
    propext via well-founded recursion proofs (8 modules).
  - Lens funext-by-design: higher-order Lens equality requires
    funext on the combine field — restating it would redefine what
    Lens IS (~18 modules under SEALED_DIRTY_PREFIXES).
  - SemanticAtom: Iff/propAsDistinguishing inherently uses propext
    (the "atom of meaning" thesis).
  - Math.Infinity.Godel: Cantor-style countability/equipotence
    proofs use Iff between cardinality propositions.
  - DyadicTrajectory: Cauchy-limit structural inequality preserved by
    ∅-axiom regime; documented in `seed/RESOLUTION_LIMIT_SPEC.md` §1.
  - Bridges: intentional axiom-demonstration cluster.

**This is the canonical 213 axiom standard** (formalized 2026-05-02,
CLAUDE.md `## Strict ∅-axiom standard`).  The 213 axiom set is ∅.

A theorem in `lean/E213/` meets the standard iff `#print axioms`
returns:
> "does not depend on any axioms"

Equivalently: no `propext`, no `Quot.sound`, no `Classical.choice`,
no `native_decide`, no `sorryAx`.

This file maintains the running catalog of theorems that meet the
standard.  Theorems still on the migration backlog
(carrying `[propext, Quot.sound]` from `omega` / `funext` / etc.) are
listed in CLAUDE.md `## Strict ∅-axiom standard → Migration backlog`.

Verification: `python3 tools/scan_axioms.py <module>` — every
theorem reports `[PURE]` (meets the standard) or `[DIRTY]` with
the exact axiom dependency listed.

## Top-level achievements (all STRICT 0-AXIOM)

| theorem | content |
|---|---|
| `validation_standard_capstone` | CLAUDE.md Standards #1+#2 met |
| `pure_atomic_observables_capstone` | 17-conjunct atomic ratios |
| `finitist_observable_chain` | 4 observables share N_U |
| `n_resolution_self_consistent` | N_U = d^(d²) self-referential |
| `fractal_lens_cardinality_capstone` | Lens count at fractal level |
| `alpha_em_master_capstone` | α_em finitist with all corrections |
| `alpha_em_so10_capstone` | SO(10) tail correction |
| `alpha_em_gram_capstone` | Gram self-energy correction |

## STRICT 0-AXIOM additions from Phase 5 batch 1+2 (2026-05-01)

Batch 1 (commit 08b02e1, omega→decide on trivial bounds):

| theorem | content |
|---|---|
| `pellFSMmod3_has_degree2` | Pell-mod-3 has algebraic degree ≤ 2 |
| `tribFSMmod2_has_degree3` | Tribonacci-mod-2 has algebraic degree ≤ 3 |
| `pisano_crt_framework_complete` | full Pisano CRT framework (was strict 0 already, retained) |

Batch 2 (commit 1cc9667, omega→Nat-lemma in BitFSM core):

| theorem | content |
|---|---|
| `fsmJointAt` | joint state encoding for BitFSM signature trajectory |
| `jointState`  | joint state encoding (general, ForwardPeriodicity) |
| `bs_periodic_multiple` | bs(n+kp)=bs(n) at multiples of period |

(Sample — full list grows as we audit downstream theorems whose
last-mile dependency was a trivial `by omega` decidable bound.)

## Number theory generals (STRICT 0-AXIOM after omega→Nat.succ_add)

| theorem | content |
|---|---|
| `ArithFSM2.run_period_of_init` | universal Pisano period theorem |
| `ArithFSM2.bits_period_of_init` | universal bits period |
| `ArithFSM3.run_period_of_init` | cubic-class universal period |
| `signature_period_of_bits_period_and_anchor` | universal sig period (TIGHT) |
| `pellFSMmod{11,19,31,47,59}_signature_period_X` | TIGHT sig instances (5×) |
| `pellFSMmod{3,5}_signature_period_X` | TIGHT sig instances (2×) |
| `tribFSMmod{3,5,19,29,31}_bits_period_X` | Tribonacci doubling bits |
| `pellFSMmod47_bits_period_48` | triple-anchor reshape via rfl |

## Pisano predictor + Legendre (STRICT 0-AXIOM after obtain→.proj)

| theorem | content |
|---|---|
| `legendre213` | 213-native Legendre symbol (definition) |
| `pisano_predict` / `_correct` | Pell-5 predictor base |
| `pisano_predict_realises_pell` | 4-prime Pell match |
| `pisano_predict_correct_6` / `_realises_pell_6` | 6-prime Pell |
| `pisano_predict_realises_pell_7` | 7-prime Pell |
| `pisano_predict_realises_pell_8` | 8-prime Pell |
| `pisano_predict_realises_pell_11` | 11-prime Pell |
| `pisano_predict_realises_pell_14` | 14-prime Pell |
| `pisano_predict_realises_pell_17` | 17-prime Pell |
| `signature_predict_realises_pell_7` | 7-prime signature |
| `two_layer_predictor_capstone` | Bit + sig layers bundled |
| `fib_pisano_predict_realises_8` | 8-prime Fibonacci |
| `legendre_5_mod_X` (X=13..89) | 14 Legendre symbols |
| `pellProper_8prime_capstone` | Pell-proper 8-prime |
| `three_family_pisano_capstone` | 3-family Galois capstone |
| `pellProper{3,5,7}_run_period_*` | 3 PellProper TIGHT |
| `pellProper{11,13,17,19,23}_bits_period_*` | 5 PellProper bits |

## Atomic identities (all STRICT 0-AXIOM via decide)

  - All Famous Coincidences (I-IV)
  - All Magic Numbers atomic
  - Per-prime Pisano (Pell, Pell-proper, Fibonacci, Tribonacci)
  - All atomic structural identities (NS·NT=6, d²-1=24, etc.)

## Significance

STRICT 0-AXIOM is the **absolute best** epistemic position in
Lean.  These theorems are checked by Lean's kernel WITHOUT any
axiom dependence — purely definitional.

External reviewers cannot challenge these via "what if propext
is wrong" since propext is not used.

## omega → propext lesson

Lean's `omega` tactic typically introduces propext + Quot.sound
dependencies.  Replacing omega with explicit kernel-level Nat
lemmas (Nat.succ_add, Nat.zero_add, etc.) UPGRADES proofs to
STRICT 0-AXIOM.

Example (commit 304723f):
  Before: `have : k+1+N = (k+N)+1 := by omega`  → propext dep
  After:  `rw [Nat.succ_add k N]`  → STRICT 0-AXIOM

## omega → decide lesson (Phase 5 batch 1, commit 08b02e1)

For `by omega` calls used purely for **decidable bounds on literals**
(e.g. `(by omega : 0 < 3)` or `(by omega : 1 < 5)`), `by decide`
is a strict 0-axiom drop-in.  In Phase 5 batch 1, 111 such
omega calls across 19 files in `Math/Cohomology/Dyadic/`
were converted, with the following measured upgrades:

  - `pellFSMmod3_has_degree2` : [propext, Quot.sound] → STRICT 0
  - `tribFSMmod2_has_degree3` : [propext, Quot.sound] → STRICT 0
  - `number_theory_213_capstone` (v1) : [propext, Quot.sound] → [propext]
  - `number_theory_213_capstone_v2`    : [propext, Quot.sound] → [propext]
  - `number_theory_213_capstone_v3`    : already [propext]
  - `pell_crt_capstone`, `pell_crt_fsm_capstone` : [propext] (kept)
  - `pisano_crt_framework_complete`   : STRICT 0 (kept)
  - `pellLens_3x5_period_20` (etc.)   : [propext] (kept)

The Quot.sound was being dragged in by inner `omega` calls in the
HasDegree witnesses (`⟨n, by omega, m, fun _ => rfl⟩`) — pure decidable
positivity that `decide` handles strictly axiom-free.  Capstones
dropping Quot.sound is a **genuine epistemic upgrade** at the trust
contract level: anything ≤ {propext, Quot.sound} is DRLT-allowed,
but the strict-0 standard rejects Quot.sound — so v1 and v2 now
qualify for the broader-still "no quotient axiom" tier.

## Audit command

```
cat > /tmp/axcheck.lean << END
import <module>
#print axioms <theorem>
END
cd lean && lake env lean /tmp/axcheck.lean
```

If output is "does not depend on any axioms", STRICT 0-AXIOM.

## Future cleanup

Many theorems at ≤ {propext, Quot.sound} could be upgraded by:
  1. Replacing omega with kernel-level lemmas
  2. Replacing simp[...] (uses propext) with rw
  3. Avoiding funext (uses Quot.sound) when not needed

Estimated upgrades: ~50-100 theorems possible.

## Cross-reference

  - `CAPSTONE_INDEX.md` — all capstones (mixed axiom levels)
  - `LESSONS_LEARNED.md` — finitist guardrails
  - `HANDOFF.md` — current state

**2026-05-09 (later, marathon batches 1-12 continued)**: 30 theorems
converted to ∅-axiom (with some net adjustments due to new helpers).
Final scan: **2542 PURE / 144 DIRTY / 0 sealed**.

Cumulative session reduction: **164 → 144 DIRTY (12.2% reduction)**.

Additional modules PURE in batches 11-12:
- E213.Lib.Math.Choice.Canonical (was 1 dirty)
- E213.Lens.Compose.OnLensImage (4 → 2, 2 fixes)

## 2026-05-20 — Deep philosophical revision pass additions

New PURE theorems from the 14-agent audit + revision pass.  All
verified `#print axioms` returns "does not depend on any axioms".

### Flat ontology + closure (§9.3 realisation)

| Module | PURE count | Highlights |
|---|---|---|
| `E213.Lens.FlatOntology` | 12 | `Object1`, `Type213`, `UnaryType`, `Relation`, `eqRelation_refl/symm`, `functionAsRelation_functional`, `lensBoolAsType`, `lensFibreType` |
| `E213.Lens.PredicateSelfEncoding` | 7 | `truthTableNat`, `predicateToRaw`, `predicate_self_encoding_closure`, `predicateToRaw_kernel`, `predicateToRaw_injective_on_prefix` |

### K_∞ ≡ point at raw (§9.5 realisation)

| Module | PURE count | Highlights |
|---|---|---|
| `E213.Lens.RawTopology` | 7 | merged-and-deduplicated: indiscrete bookend (`constLens_view_eq`, `constLens_equiv`, `constLens_is_top`, `k_infty_at_raw_bundle`), discrete bookend (`discrete_kernel_eq`, `discrete_distinguishes`), and the two-bookend topology bundle (`topology_two_bookends`).  `UndifferentiatedRaw.lean` merged in (was 3 theorems, all duplicates of indiscrete-bookend content). |

### Three-direction uniqueness bundle (§1.3 realisation)

| Module | PURE count | Highlights |
|---|---|---|
| `E213.Meta.ThreeDirectionUniqueness` | 1 | `three_direction_uniqueness` — single statement bundling below/sideways/above closures |

### Self-completion (§8.6 realisation)

| Module | PURE count | Highlights |
|---|---|---|
| `E213.Lens.SelfCompletion` | 6 | atomic Clause 1 visibility (`view_at_a_uses_base_a`, `view_at_b_uses_base_b`, `atomic_self_completion_bundle`), slash-side Clauses 2-4 visibility (`view_slash_uses_combine`, `full_self_completion_bundle`, `leaves_self_completion`) |

### Möbius frozen + dynamic dualism (§3.4 / §8.7 realisation)

| Theorem | content |
|---|---|
| `mobius_213_char_poly_at_trace` | char poly evaluated at trace = det (φ², 1/φ² as eigenvalues) |
| `mobius_213_pell_unit_invariant` | `num_n · den_{n+1} − num_{n+1} · den_n = -1` across 8 convergent layers in one bundle (witnesses det [[2,1],[1,1]] = 1 lifted to consecutive-pair determinants) |
| `P_numerator_values` / `P_denominator_values` | concrete Pell convergent values for k = 0..8 |

### Möbius ↔ Fibonacci structural bridge

| Theorem | content |
|---|---|
| `F12_eq_edge_squared` | F_12 = (c·NS·NT)² — squared Phase-2 edge count, the one notable structural reading among F_11..F_15 |
| `mobius_fibonacci_bridge` | 16-conjunct identity: Pell-denominator layer k = F_{2k+1} (odd Fibonacci), Pell-numerator layer k = F_{2k+2} (even Fibonacci), for k = 0..7.  Same integer skeleton, two structural Lenses |

### 4-clause forcing chain (§4.5)

| Theorem | content |
|---|---|
| `raw_forcing_chain_unified` | positive complement to `raw_minimality_capstone`; documents the chain 1 → 2 → 3 → 4 |

### Cross-observable precision bridge (NS·NT·π⁵ block)

| Module | PURE count | Highlights |
|---|---|---|
| `E213.Lib.Physics.Capstones.NSNTPi5Block` | 1 | `ns_nt_pi5_block_capstone` — 10-conjunct cross-observable bridge linking m_p/m_e and 1/α_em(IR) gap as two readings of the same NS·NT·π⁵ skeleton (atomic anchors + shared block + both precision brackets in one statement) |
| `E213.Lib.Physics.AlphaEM.PiFiveGap` | +2 (17 → 19) | `pi5_residual_thirteen_bracket`, `pi5_ns_nt_block` — strict bracket forms of the precision claim |

**Cumulative new PURE from this session, post-reduction: ~55** (raw count is lower since session-12 reductions collapsed enumerations into single bundles).  All audit-verified.

## 2026-05-22 — Cup-Leibniz general transfer + 6-theorem + alive closure

### ∀(n, k) kSubset bijection + ∀(n, k, l) Fin-bridge

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Math.Cohomology.Cup.KSubsetStructural` | 9 (+6 helpers) | `kSubset_length`, `kSubset_all_lt`, `kSubset_injective`; helpers `nat_add_sub_cancel`, `nat_sub_lt_sub_right`, `list_length_append_singleton`, `nat_sub_pos_of_lt` (propext-free Lean-core replacements) |
| `E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtripGeneral` | 7 | `find_range_witness` (avoids `List.range_succ` propext), `roundtrip_n_1`, `roundtrip_n_1_fin`, `roundtrip_n_k`, `roundtrip_n_k_fin` |
| `E213.Lib.Math.Cohomology.Cup.FinBridgeGeneral` | 7 | `kSubset_take_eq`, `kSubset_drop_eq`, `frontIdx`, `backIdx`, `frontIdx_lt`, `backIdx_lt`, **`cup_unfold_general`** — ∀(n,k,l) capstone subsuming the Δ⁴-specific FinBridge.lean tables |

### The 6-theorem (G87 §5 closure)

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Math.CayleyDickson.Integer.ZOmegaUnits` | 18 | `units6` (6 Eisenstein units), `Zeta6 = 1+ω` order-6 generator, cyclic structure, count bridges `units_count_eq_NSNT / _six / _d_plus_one / _three_factorial`, `int_sq_le_one` diophantine helper |
| `E213.Theory.SixTheorem` | 11 | 10 reading theorems + `★ six_theorem` master — all ten "6" readings unified on `\|units6\| = NS·NT = 6` with χ-sum bridge `χ(Δ⁴) + χ(K_{3,2}^{(c=2)}) = -(\|units6\| : Int)` |

### Alive gap closure (G87 §11)

| Module | PURE | Highlights |
|---|---|---|
| `E213.Theory.Atomicity.AliveDerivation` | 7 | `IsSelfPaired`, `IsClause4Alive`, `parity_iff_not_self_paired`, **★ `alive_iff_clause4_alive`** dissolves the postulated alive predicate into Clause 4 of the 213 axiom applied recursively at count-Lens group level; `atomic_iff_five_via_clause4` reformulates atomicity |

### Pentagonal closure matrix-level (G78 stale-path fix)

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Math.Mobius213ModFive` | 9 | `P5_11/12/22_mod_5`, **`P_pow_5_eq_neg_I_mod_5`**, **`P_pow_10_eq_I_mod_5`**, `pentagonal_closure_signature` — consolidates G78's headline matrix-level claims |

**Cumulative new PURE this session: ~68** across 8 new files + 3 doc updates.  All audit-verified.

## 2026-05-22 — C3 chain Phase 1: Aut(K) as Type

Phase 1 of the **C3 chain** (G87 §4) — lifting `Aut(K_{3,2}^{(c=2)})`
from Nat-only `aut_order = 768` to a Lean `Type` via the explicit
direct-product structure `Sym3 × Sym2 × C2_6`.  This is the
foundational layer for downstream Group / module / representation
work (Phases 2–6).

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Physics.Symmetry.AutKType` | 16 | `Sym3 := Fin 6`, `Sym2 := Fin 2`, `C2_6 := Fin 64`, **`Aut_K := Sym3 × Sym2 × C2_6`** as a Type; `DecidableEq` instances on all four; element constructors (`Sym3.max`, `Sym2.max`, `C2_6.max`, `Aut_K.max`, `Aut_K.one`, `Aut_K.mk`); **`component_cardinalities`** 12-conjunct bridge linking `fac NS`, `fac NT`, `2^(NS·NT)`, and `aut_order = external_order × internal_order = 768`; **`Aut_K_type_decomp`** Type-level decomposition; **`★ AutK_phase1_capstone`** — Phase-1 capstone bundling Type decomposition + identity + cardinality bridges |

## 2026-05-22 — C3 chain Phase 2: H¹(K) as explicit ℤ/2-module of rank 8

Phase 2 of the **C3 chain** — lifting `H¹(K_{3,2}^{(c=2)})` from
the Betti counting result (`V32Betti.b_1 = 8`, |H¹| = 256) to an
explicit ℤ/2-module of rank 8 with named cycle-generator basis.

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Math.Cohomology.Bipartite.H1K` | 25 | **`H1K := Fin 8 → Bool`** as the rank-8 ℤ/2-module; ℤ/2-module operations `zero`, `add` (pointwise xor), `smul` (pointwise and); pointwise module axioms `zero_add`, `add_zero`, `add_self` (char-2), `add_assoc`, `add_comm`, `zero_smul`, `one_smul` (all PURE via pointwise form avoiding funext/`Quot.sound`); 8 basis vectors `H1K.basis i` with `basis_self`, `basis_other` characterisation; `nonTreeEdges`, `nonTreeEdge` mapping H1K-coordinates to the 8 non-tree edges {1, 3, 5, 6, 7, 9, 10, 11} (spanning tree {0, 2, 4, 8}); `nonTreeEdge_enumeration` 8-conjunct decide-bridge; `H1K.rank = 8 = NS² − 1` cross-links to `V32Betti.b_1_eq_8` and `PhotonKernel.b_1_eq_8`; `H1K_basis_distinct`; `H1K_count_bridge` `\|H1K\| = 2⁸ = 256`; **`★ H1K_phase2_capstone`** — Phase-2 capstone bundling Type definition + module axioms + basis + cardinality bridges |

## 2026-05-22 — C3 chain Phase 3: Sym(3) action on K_{3,2} edges

Phase 3 of the **C3 chain** — constructs the external Sym(3)
factor of Aut(K_{3,2}^{(c=2)}) acting on the 12 edges via two
transposition generators (σ_S01, σ_S12) and verifies the full
Cayley structure.

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Physics.Symmetry.Sym3OnKEdges` | 22 | Two transposition generators **`σ_S01`**, **`σ_S12`** acting on `Fin 12` K-edges (swap S0↔S1, S1↔S2 respectively); third transposition **`σ_S02 := σ_S01 ∘ σ_S12 ∘ σ_S01`** by conjugation; 3-cycle **`ρ_S := σ_S12 ∘ σ_S01`** and `ρ_S_sq`; involution properties `σ_S01_involution`, `σ_S12_involution`, `σ_S02_involution`; order-3 properties `ρ_S_order_3`, `ρ_S_sq_order_3`; Cayley relations `σ_S01_ρ` (= σ_S02), `ρ_compose` (ρ² = ρ·ρ); edge-cochain pullback action `σ_act_E` with pointwise involution `σ_act_E_S01_involution`, `σ_act_E_S12_involution` (no funext); specific edge mappings as sanity checks; **`★ Sym3OnKEdges_phase3_capstone`** bundling all generator + Cayley + action data |

## 2026-05-22 — C3 chain Phase 4: Sym(3) descent to H¹(K) via δ⁰ equivariance

Phase 4 of the **C3 chain** — proves the edge action of Phase 3
descends to a well-defined action on H¹(K_{3,2}^{(c=2)}) by
exhibiting compatible vertex permutations and verifying δ⁰
equivariance.  This is the substantive C3-step linking the edge-
level group structure to cohomology-level group representation.

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Physics.Symmetry.Sym3OnH1K` | 16 | Vertex permutations **`φ_V_S01`**, **`φ_V_S12`** (Fin 5 → Fin 5) compatible with the edge transpositions; involution properties `φ_V_S01_involution`, `φ_V_S12_involution`; **src/tgt equivariance** `src_equiv_S01`, `tgt_equiv_S01`, `src_equiv_S12`, `tgt_equiv_S12` (decide-verified edge by edge); vertex-cochain pullback action `φ_act_V`; **`★ delta0_equiv_S01`**, **`★ delta0_equiv_S12`** — pointwise δ⁰ equivariance theorems (no funext); coboundary preservation `σ_S01_preserves_coboundaries`, `σ_S12_preserves_coboundaries` establishing well-defined descent to H¹(K); explicit non-tree edge behavior `σ_S01_nontree_1/3/6_to_tree/7`, `σ_S01_fixes_S2` documenting the basis-decomposition structure (some non-tree → tree transitions require coboundary correction); **`★ Sym3OnH1K_phase4_capstone`** — 10-conjunct Phase-4 capstone bundling all equivariance + descent data |

## 2026-05-22 — C3 chain Phase 5: Sym(3) representation matrix on H1K basis

Phase 5 of the **C3 chain** — computes the **explicit 8×8 matrix**
of σ_S01 acting on the H1K basis (the 8 non-tree edge classes),
with tree-decomposition witness for the exceptional row and full
matrix involution verification.

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Physics.Symmetry.Sym3OnH1KMatrix` | 7 | Explicit 8×8 matrix **`M_S01 : Fin 8 → H1K`** with 7 basis-to-basis permutation rows and 1 exceptional row (e_3 ↦ e_1 + e_3 + e_4 + e_6 + e_7) from tree-decomposition; **`v_tree_witness`** vertex cochain `(0,0,0,0,1)` providing the coboundary that resolves the non-tree → tree transition; **`delta0_v_tree_at_each_edge`** — 12-conjunct decide-bridge verifying which edges have tgt = vertex 4 (i.e. T_1); matrix-matrix product **`M_mul_M`** and **`★ M_S01_squared_pointwise`** — full involution verification at the matrix level (`M_S01 · M_S01 = IdMatrix`) on all 64 entries via decide; `boolTrace`, `intTrace` operations; **`boolTrace_M_S01 = false`** (mod-2 character); **`intTrace_M_S01 = 4`** (count of fixed basis vectors: e_3 diag, e_5, e_6, e_7); **`★ Sym3OnH1KMatrix_phase5_capstone`** — 11-conjunct Phase-5 capstone |

## 2026-05-22 — C3 chain Phase 6: Sym(3) Cayley structure on H1K matrix level

Phase 6 of the **C3 chain** — extends Phase 5 with the σ_S12
representation matrix (no tree corrections needed) and verifies
the full Sym(3) Cayley structure at the H1K 8×8 matrix level.

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Physics.Symmetry.Sym3OnH1KCayley` | 14 | **`M_S12`** — pure permutation matrix on H1K: identity on {e_0, e_1}, three transpositions (e_2 e_5)(e_3 e_6)(e_4 e_7); `M_S12_squared_pointwise` involution at matrix level; `boolTrace M_S12 = false`, `intTrace M_S12 = 2`; **`M_ρ := M_S12 · M_S01`** 3-cycle representation matrix; **`M_ρ_cubed_pointwise`** — full 64-entry decide on `(M_ρ)³ = I`; `boolTrace M_ρ = true`, `intTrace M_ρ = 1`; **`M_S02 := M_S01 · M_S12 · M_S01`** derived transposition matrix; `M_S02_squared_pointwise` involution; **Cayley relations** `cayley_σ_S01_sq`, `cayley_σ_S12_sq`, `cayley_ρ_cubed` realising the standard Sym(3) presentation ⟨s, t \| s² = t² = (st)³ = e⟩; **`★ Sym3OnH1KCayley_phase6_capstone`** — 10-conjunct Phase-6 capstone with conjugate-trace-agreement diagnostic (bool-trace conjugacy invariant: σ_S01, σ_S12 transpositions both → 0; σ_ρ 3-cycle → 1) |

**Cumulative new PURE this session: +100** (16 Phase 1 + 25 Phase 2 + 22 Phase 3 + 16 Phase 4 + 7 Phase 5 + 14 Phase 6 of C3 chain).

## 2026-05-22 — C3 chain Phase 7: ι: K → Δ⁴ + gluon octet identification

Phase 7 of the **C3 chain** — the inclusion `ι: K_{3,2}^{(c=2)} → Δ⁴`,
the cochain pullback `ι#: CochE(Δ⁴) → CochE(K)`, the cohomology
descent `ι*: H¹(Δ⁴) → H¹(K)`, and the **gluon octet identification**
`coker ι* = H¹(K) ≃ (F_2)^8`.

| Module | PURE | Highlights |
|---|---|---|
| `E213.Lib.Physics.Symmetry.IotaKToDelta4` | 10 | **`ι_edge : Fin 12 → Fin 10`** collapsing both multiplicities of each S-T pair to the underlying colex-indexed Δ⁴ edge (6-way pairing 2k ↔ 2k+1); `ι_edge_collapses_multiplicities`; `ι_edge_image_complement` — image omits {0, 1, 2, 9} (3 S-S edges + 1 T-T edge); cochain pullback **`ι_pullback : Cochain 5 2 → CochE`**; `ι_pullback_all_true`, `ι_pullback_edge3` sanity; **`★ kerSize_delta_5_2 = 16`** — direct 1024-case decide enumeration of `Cochain 5 2` (with `maxRecDepth 2048`) establishing `H¹(Δ⁴) = 0` (16 cocycles = 16 coboundaries since `\|im δ⁰\| = 2^(5-1) = 16`); `H1_delta4_trivial_card` 4-conjunct cardinality bridge; `ι_star_zero_on_zero` — ι* of zero is zero; `cardH1K_eq_256` cross-link to V32Betti; **`★ gluon_octet_identification`** — 5-conjunct bridge `\|coker ι*\| = \|H¹(K)\| / \|im ι*\| = 256 / 1 = 2^8`; **`★ IotaKToDelta4_phase7_capstone`** — 12-conjunct Phase-7 capstone bundling embedding + image + H¹(Δ⁴) = 0 + ι* = 0 + gluon octet identification |

**Cumulative new PURE this session: +110** (16 + 25 + 22 + 16 + 7 + 14 + 10 across 7 phases of C3 chain).

The C3 chain through Phase 7 establishes the full **gauge-emergence
narrative**: from `Aut(K)` Type (Phase 1) through Sym(3) representation
on H¹(K) at the explicit matrix level (Phases 3–6) to the **gluon
octet identification** `H¹(K) ≃ (F_2)^8 = coker ι*` (Phase 7).

Physics reading: the 8 generators of H¹(K) are the 8 cycles in
K_{3,2}^{(c=2)} that **remain non-trivial after embedding into the
contractible Δ⁴** — match the 8 gluons of the SU(3) adjoint
representation (the QCD octet).

The C3 chain through Phase 6 establishes the complete 8-dim
Sym(3) representation on H¹(K_{3,2}^{(c=2)}) at the matrix level:

  · Aut(K) as a Type with cardinality 768 (Phase 1)
  · H¹(K) as an explicit rank-8 ℤ/2-module (Phase 2)
  · Sym(3) generators acting on K-edges with full Cayley structure (Phase 3)
  · δ⁰ equivariance ⇒ well-defined descent to H¹(K) (Phase 4)
  · Explicit 8×8 representation matrix M_S01 with tree-decomp (Phase 5)
  · Full Sym(3) presentation ⟨s, t | s² = t² = (st)³ = e⟩ realised
    at the H1K matrix level; conjugacy invariance verified via
    bool-trace (Phase 6)

Diagnostic finding (Phase 6): integer-trace data is basis-dependent
(tr(M_S01) = 4 ≠ tr(M_S12) = 2 despite σ_S01, σ_S12 conjugate in
Sym(3)); the basis-independent F_2 trace (bool-trace) correctly
gives both = 0 for transpositions and 1 for 3-cycles.

Remaining for the gauge-emergence narrative:
  · Phase 7: Sym(3)-irrep decomposition over F_2 (modular case
    where 1 = sign, hence fewer irreducibles than over Q)
  · Phase 8: ι*: H¹(Δ⁴) → H¹(K) and connection to SU(3) adjoint
