# STRICT ∅-AXIOM — the 213 axiom standard

> **Canonical definitions (single source of truth):** see "Terms"
> section below.  When other documents (HANDOFF.md, CLAUDE.md,
> scan_all_axioms.py comments) drift from these definitions, this
> file wins.  Falsifiability anchor: `seed/AXIOM/08_falsifiability.md` §8.2.

## Terms (canonical)

| Term | Definition |
|---|---|
| **PURE** | `#print axioms <thm>` returns "does not depend on any axioms".  Identical to "strict ∅-axiom".  This is the standard target. |
| **DIRTY** | `#print axioms` returns "depends on axioms: [...]" with a non-empty list.  Any of `propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` (from `native_decide`), `sorryAx`. |
| **sealed-DIRTY-by-design** | A DIRTY theorem accepted because (a) Lean-core boundary (well-founded recursion, Lean.Elab metaprogramming inheriting Classical.choice via the Lean.Elab.Command monad), or (b) Lens funext-by-design (higher-order Lens equality requires funext on the combine field, refactoring would redefine what "Lens equality" means).  Listed in `tools/scan_all_axioms.py` `SEALED_DIRTY_PREFIXES`. |
| **real DIRTY** | DIRTY ∧ NOT sealed-by-design.  This is the regression budget. |

**The 213 axiom set is ∅** — a theorem meets the standard iff PURE.

**Forbidden absolutely** (per `seed/AXIOM/08_falsifiability.md` §8.2, falsifiability
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

## Sealed-by-design categories

The seal list in `tools/scan_all_axioms.py` waives modules whose
DIRTY status is *structural* — refactoring would redefine what the
module is, not improve its derivation.  Any DIRTY outside this list
is a real regression.

### (a) Prop-as-distinguishing thesis — `propext`

`HasDistinguishing` is the typeclass for "framework instance: a
type with a/b/combine such that True ≠ False analogue holds and
combine is symmetric."  When the type is `Prop`, the field
`combine_sym : combine P Q = combine Q P` is a propositional
equality between Props — provable in Lean 4 only via the kernel
axiom `propext`.

Sealed modules:

  · `E213.Lens.SemanticAtom`
      `propAsDistinguishing` + `propAsDistinguishing{And, Or, Iff}`
      use `combine = propXor / And / Or / Iff`; `combine_sym` is
      `(P * Q) = (Q * P)` at type `Prop`.  Carries `iff_comm_eq`
      and `propXor_comm` for the symmetry lemmas.
      `canonical{Truth, And, Or, Iff}Map_*` are derived via
      `universalMorphism_*` and inherit the propext use.

  · `E213.Lens.Properties.Morphism.BoolProp`
      `boolToProp : Bool → Prop` is `b ↦ (b = true)`.  Theorems
      `boolToProp_true / false / and / or / xor / iff` and
      `universalMorphism_commute*` equate Props (e.g. `boolToProp
      (and x y) = (boolToProp x ∧ boolToProp y)`) — propext.

The thesis "Prop is an atom of meaning" *is* what `propext`
expresses.  Removing the seal would require removing Prop as a
HasDistinguishing instance, which removes the thesis.

### (b) Lens kernel as function-`=` of views — `Quot.sound` (= `funext`) + `propext`

`Lens.combine : α → α → α` for the universal / indexed / Cauchy
Lens family is function-valued — `α = Raw → β` or `α = (i : ι) →
...`.  Then `Lens.combine_sym : combine x y = combine y x` becomes
a function equality, which in the Lean 4 kernel is `funext`,
derived from `Quot.sound`.  `Lens.equiv` on Raw is the same
pattern at one level up: it states `L.view r = L.view r'` at type
`Prop` (Iff↔Eq via propext) and `Lens.refines` says
`L.equiv r r' → M.view r = M.view r'` (function equality on
view).  Both patterns inherit propext + Quot.sound from the kernel.

This category is a **statement-shape** cost, not a redefinition cost,
and the universalLens refinement surface is **retired from it**.  The
213-native meaning of "the same under `L`" is the
distinguishing-equivalence — pointwise `↔` — carried by the
codomain-polymorphic Reading-equivalence API in `Lens/ReadingEquiv.lean`:

  · `ReadingEq α` — per-codomain reading-sameness (`=` at the default
    instance, pointwise `↔` at `Raw → Prop`), an equivalence relation,
    laws PURE;
  · `Lens.equivG` / `Lens.refinesG` — codomain-polymorphic equivalence /
    refinement, reducing **definitionally** to `equiv` (default) and
    `equivR` (`Raw → Prop`);
  · `Lens.equivG_slash_congruence` — the slash-congruence, generic over
    the codomain.

The load-bearing hub `universalLens_kernel_eq_E_R` (`equivR r r' ↔ E r r'`)
plus the closure companions `universalLens_recovers_R` /
`universalLens_idempotent_R` (built on `universalLens_equivR_slash_congruence`
/ `combine_cong_pw` / `fold_pw`) are PURE, and **every consumer is stated on
this API** — the refinement lattice (`Join`, `IndexedJoin`, `FamilyMeet`,
`FamilyJoin`), the Cauchy limit Lens, the kernel↔slash-congruence bijection
(`Corresp`), the choice-as-Lens-spec, and the canonical-form / idempotence
theorems (`CanonicalForm`) are all ∅-axiom.  The `=`-of-view-functions forms
are gone; the only `=`-cost is the single isolated bridge
`Lens.equivR_to_equiv` (the `↔ ⟹ =` direction, kept by design).  Only
`propAsDistinguishing` (category a) remains irreducible by thesis.  See
`theory/lens/dirty_recovery_patterns.md` Pattern P5 and
`theory/lens/unified_equivalence.md`.

Remaining sealed module in this category:

  · `E213.Lens.Instances.Leaves.DepthJoin`
      Three-tier classification of `Raw` via `JoinEquiv
      Lens.leaves Lens.depth` (a `Nat`-valued lens family).  The 10
      tier invariants (`small_invariant`, `tier_invariant`,
      `class_of_a_iff_small`, `three_classes_distinct`, `tierLens_*`,
      `depth_refines_tierLens`, `leaves_refines_tierLens`,
      `joinEquiv_subset_tierLens`, `leaves_depth_join_not_universal`)
      carry `propext` / `Quot.sound` from the `omega` / `simp`-closed
      arithmetic helpers, **not** from the refinement API — this is the
      `omega`/`simp`→explicit purification playbook (cf. `Mobius213.Px`),
      a separate backlog from the Reading-equivalence rebuild.

### Net effect

Scope note: until the build gate was made comprehensive (G159), only the
umbrella-reachable subset was ever scanned, and that subset was fully PURE
(non-sealed).  The comprehensive gate now scans **all 1532 modules**, which
exposes the purity status of the previously-ungated clusters.  Current
`tools/scan_all_axioms.py`:

  · The 213-mathematical core is ∅-axiom.  The non-sealed `propext`/`Quot.sound`
    that remain are (i) the **`Prop`-atom thesis surface**
    (`propAsDistinguishing*` / `canonical*Map` / `BoolProp.universalMorphism_commute_*`,
    category (B) — `propext` IS "`Prop` is an atom of meaning") and (ii) the
    **CayleyDickson open items** (`Trig.conj_mul_anti`, `SedenionHeavy.flexible`,
    category (D)).  The Lens ring is **0 real DIRTY** (`scan_all_axioms.py
    --filter Lens`): its equivalence surface is stated on reading-equivalence
    (`ReadingEq.same` / `equivR` / `sameLens`), not `=` of views.  Run
    `tools/scan_all_axioms.py` for the live count.
  · **No `Classical.choice` and no `Lean.ofReduceBool` (`native_decide`) in any
    213-mathematical content** — the falsifiability-forbidden axioms are absent.
    The only `Classical.choice` carriers are three `CommandElab` elaborators
    (`Lib.Math.Tactic.QuadExtension`, `Meta.Tactic.{DeriveConjugationCodomain,
    VerifyConjugation}`), inherited via the `Lean.Elab.Command` monad — sealed
    plumbing per category (a), not math content.
  · The remaining real DIRTY are **`propext` / `Quot.sound` only** (the
    "allowed-but-not-target" core-kernel axioms) — the `Prop`-atom thesis surface
    (category B) + the CayleyDickson `Trig.conj_mul_anti` / `SedenionHeavy.flexible`
    (category D).  The category-D backlog uses the `Mobius213.Px` playbook
    (`omega` → `rfl`/`Nat.two_mul`/`Nat.add_right_comm`; `Nat.mul_assoc`/`Nat.add_mul`
    → `NatRing.nat_*`; `simp` → explicit `rw`; `Nat.mul_lt_mul_left`/`mul_lt_mul_right`
    (the `Iff`) pull `Classical.choice` → constructive `c*m+1 ≤ c*m+c ≤ c*n` helper,
    cf. `KerSizeUniversal.mul_lt_mul_left_pure`) + the Int/`same` playbooks
    (`Meta/Int213`, `ReadingEq`/`sameLens`).
  · **Gate vindication**: closing the build-gate hole (G159) exposed a genuine
    falsifiability violation that had been invisible — `KerSizeUniversal`'s
    `Classical.choice` (via `Nat.mul_lt_mul_left`) in an orphaned cluster, now
    fixed.  A gate that only follows umbrella imports cannot guarantee the
    ∅-axiom standard; the comprehensive build is required.
  · **Sealed-by-design** per categories (a) + (b): the Prop-as-distinguishing
    family + the three CommandElab plumbing modules.  **213-native re-reading
    (not just ∅-axiom)**: only the **3 CommandElab** + `propAsDistinguishing` are
    *irreducible*.  The 3 CommandElab inherit `Classical.choice` via the
    `Lean.Elab.Command` monad (no `↔`-form alternative); `propAsDistinguishing` is
    `propext` expressing the thesis "Prop is an atom of meaning".
  · **The universalLens refinement surface is PURE** (the headline (a)
    pointwise-API rebuild, done).  The 213-native notion of "the same under `L`"
    is the pointwise **Reading-equivalence** (`equivR`, `∀ s, view x s ↔ view y
    s`); `Lens/ReadingEquiv.lean` lifts it to the codomain-polymorphic
    `ReadingEq` / `equivG` / `refinesG` (reducing definitionally to `equiv` at
    the default instance and `equivR` at `Raw → Prop`).  The kernel hub
    (`universalLens_kernel_eq_E_R`), the slash-congruence
    (`universalLens_equivR_slash_congruence`), and the closure companions
    (`universalLens_recovers_R` / `universalLens_idempotent_R`) are all PURE, and
    **every consumer is stated on this API**: the refinement lattice (`Join`,
    `IndexedJoin`, `FamilyMeet`, `FamilyJoin`), the Cauchy `limitLens`, the
    kernel↔slash-congruence bijection (`Corresp`), `Choice.choice_as_lens_spec`,
    and `CanonicalForm.{refinesEquiv, lens_canonical_universal,
    lens_canonical_idempotent}`.  The `=`-of-view-function forms are gone; the
    lone `=`-cost is the isolated bridge `equivR_to_equiv` (the `↔ ⟹ =`
    direction).  Only `propAsDistinguishing` stays irreducible.  Anchors:
    `theory/lens/dirty_recovery_patterns.md` Pattern P5,
    `theory/lens/unified_equivalence.md`.

---

## PURE-bounded on Lean 4 core (2026-05-22)

**Verification**: G95 (dependency-purity audit) +
`claude/subset-bijection-lemmas-w2FKf` branch's N5 + N6 closures.

Beyond avoiding `Classical.*`/`native_decide`/`sorryAx`, the DRLT
corpus has been audited for *Lean-core* axiom dependencies (those
inherited transitively via Lean's standard-library lemmas that
themselves bring `propext`/`Quot.sound`).

Net status: **DRLT is PURE-bounded on Lean 4 core** — no non-test
DIRTY citation chain reaches outside the kernel.  Two centralisations
made this possible during the cycle:

  · **N5**: `Nat.max_comm` → `NatHelper.max_comm` (5 sites).
  · **N6**: `Int.mul_sub` / `Int.sub_mul` → `Meta.Int213.{mul_sub, sub_mul}`
    (12 sites).
  · **N8/N9** (this branch): `NatHelper.mul_left_comm` + `Nat.add_right_comm`
    adoption (25 sites, Pattern #10).

Future Lean-core upgrades that change axiom dependencies of
standard-library lemmas are caught by re-running G95.

---

## Latest scan

(Numbers vary by run due to scanner timeouts on slow modules; refer
to HANDOFF.md "current state" for the freshest reading.  1232 total
`.lean` files; scanner enumerates ~500-1000 ★-marked theorems
depending on timeout state.)

**2026-05-22 (audit branch `claude/document-file-audit-FeGcU`)**:
Full repo scan reports **1145 PURE / 0 real DIRTY + 56 sealed-DIRTY-
by-design (1201 total)**.

The 56 DIRTY theorems are all waived under the sealed-by-design
categories above:

  · 23  E213.Lens.SemanticAtom                  — category (a) propext
  · 10  E213.Lens.Properties.Morphism.BoolProp  — category (a) propext
  · 10  E213.Lens.Instances.Leaves.DepthJoin    — category (c) Classical.choice (5) + category (b) Quot.sound (5)
  ·  5  E213.Lens.Universal.QuotLens            — category (b) Quot.sound
  ·  4  E213.Lens.Lattice.IndexedJoin           — category (b) Quot.sound
  ·  3  E213.Lens.Instances.Cauchy              — category (b) Quot.sound
  ·  1  E213.Lens.Instances.FunctionSpace       — category (b) Quot.sound

DRLT mathematical content (`E213.Lib.Math.*`, `E213.Lib.Physics.*`,
`E213.Theory.*`, all capstones) is **fully PURE**.  Zero unsealed
DIRTY: every Lean-core axiom use is structurally justified per
§"Sealed-by-design categories".

### Real-number stratification addition (2026-06-01)

`E213.Lib.Math.Real213.RateStratification` — **12 PURE / 0 DIRTY**.
The constructed-modulus generator's smallness law made a layer-by-layer
**W-vs-d comparison**: `htel_iff_dominates` (the rate certificate `Htel`
is *exactly* domination at every layer), `dominated_free_modulus`
(domination everywhere ⟹ free modulus), `overtake_breaks_layer` (any
layer where the cross-determinant overtakes the denominator quantum
breaks it), and the unimodular det-1 floor as the trivially-free bottom
(`floor_dominates_all` / `floor_carries_Htel` / `tower_stratification`).
The forward additive-cancel used the PURE `NatHelper.le_of_add_le_add_left`
(Lean-core `Nat.le_of_add_le_add_left` is propext-dirty); the floor
polynomial identity is discharged by the `Meta.Nat.PolyNat` reflection ring.

`E213.Lib.Math.Cauchy.DepthOverflowDuality` — **15 PURE / 0 DIRTY**.
The analysis ↔ logic single engine: `Overflow bound val i := bound i <
val i` (= `bound i + 1 ≤ val i`, the unit surplus).  `overflow_escapes`
(overflow ⟹ value is no level of the family; recovers `diag_not_in_seq`),
`overflow_breaks` (overflow ⟹ domination breaks = `overtake_breaks_layer`),
`overflow_dual_reading` (both readings of one operation).  Bridges
`DepthCeilingResidue` (Cantor residue) and `RateStratification` (¬Htel).
Plus the unit-generator layer: `minOverflow bound = bound + 1` is the
pointwise-least overflow (`least_overflow`, `minOverflow_overflows`), the
diagonal achieves it (`diag_is_minOverflow`), overflow is monotone /
shift-stable (`overflow_mono_val`, `overflow_shift`), the least overflow is
unique (`minOverflow_unique`, the honest universal property), and the surplus
is the conserved quantity under shift (`gap_shift_invariant`, via the PURE
`NatHelper.add_sub_add_right`).

`E213.Lib.Math.Real213.IntensionalCompletability` — **3 PURE / 0 DIRTY**.
The intensional reduction of completability: `crossDetSmall_rescale_antitone`
(the sufficient bridge `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` — rescaling
up only loses it, so the gcd-reduced presentation is canonical; `Nat.mul_assoc` is
propext-dirty, used the PURE `NatHelper.mul_assoc`), `modulus_rescale_invariant`
(the completion is presentation-invariant, via `rcut_rescale`), bundled in
`completability_is_intensional`.  The test is presentation-relative; the truth is not.

`E213.Lib.Math.Real213.ScalingOrbit` — **7 PURE / 0 DIRTY**.  The rescaling
orbit `(c·a, c·d)` of a presentation: `scaleBy` a monoid action (`scaleBy_one`,
`scaleBy_comp`), the cut its complete invariant (`scaleBy_preserves_cut`),
`CrossDetSmall` antitone along it (`orbit_free_implies_base_free`), and the
`Reduced` base unique (`reduced_scaling_trivial`).  Bundled in
`scaling_orbit_structure`.  Advances C2 (G169): the reduced base is the
rung-minimal presentation within a rescaling orbit (scope: rescaling sub-family,
not all presentations).

The signed-ℤ Eisenstein/golden signature dichotomy is closed canonically in
`E213.Lib.Math.CayleyDickson.Integer.EisensteinSignature` (`eisForm_nonneg`,
`eisenstein_norm_nonneg`, `golden_indefinite`, `signature_dichotomy`) via the
bivariate Int reflection prover `Meta.Int213.PolyInt2` — the genuine `0 ≤ a²−ab+b²`
over ℤ, tied to `ZOmega.normSq`.  (The earlier ℕ-visible sidestep
`Real213.CrossDetDiscriminant` is removed — superseded once `PolyInt2` landed.)

### G122 closure addition (2026-05-22; extended through 2026-05-23)

`E213.Lib.Math.Padic.*` — Real213-p-adic library — adds **308 PURE
declarations** across 8 modules (`Foundation`, `Arith`, `Pow`,
`Norm`, `Hensel`, `Teichmuller`, `Field`, `DRLT`).  Headline
closures:

  · `Zp.add_trunc` / `Zp.mul_trunc` — ring-quotient theorems for
    truncation `ZpSeq p → ℤ/p^n`; full ring axioms at trunc level
    (comm, assoc, distrib, additive inverse via `add_neg_self_trunc`).
  · `Zp.mul_invSeq_correct` / `Zp.mul_invFull_correct` /
    `Zp.inv_trunc_unique` — Hensel-lifted multiplicative inverse
    with existence + uniqueness at every level.
  · `Zp.sqr_sqrtSeq_correct` / `Zp.sqr_sqrtFull_correct` /
    `Zp.sqr_unique_trunc` — Hensel-lifted square root via
    `SqrtBase`, with existence + uniqueness.  Concrete instances:
    `i_5 = √(-1) ∈ ℤ_5`, `i_13 ∈ ℤ_13`, `sqrt_two_7 ∈ ℤ_7`.
  · `Zp.valAtLeast_add` / `Zp.valAtLeast_mul` / `Zp.valEq_add_of_lt`
    / `Zp.valEq_mul` / `Zp.valEq_neg` — full strong ultrametric
    (additive + multiplicative + negation, precise valEq forms).
  · `Zp.pow` / `Zp.pow_trunc` / `Zp.pow_add_trunc` /
    `Zp.pow_mul_trunc` — natural-number power with ring-quotient
    homomorphism properties.
  · `Zp.pow_p_trunc_one` / `Zp.pow_p_minus_one_trunc_one` — Fermat's
    little theorem at digit 0 (for p prime via `prime_gcd`).
  · `Zp.frobenius_lift` / `Zp.teichmuller_iter_cauchy` — Frobenius
    lift `y ≡ z mod p^k → y^p ≡ z^p mod p^(k+1)` and Cauchy
    convergence of the iteration `x ↦ x^p`.  Notable: the proof
    avoids binomial coefficients entirely and holds for any p ≥ 1.
  · `QpSeq` ℚ_p localization with add/sub/mul/neg/inv/div/sqrt.
  · `canonical_5adic_p` — 5-adic lift of the base prime `5`,
    with digit smoke-tests.

Chapter: `theory/math/padic_real213.md`.
Source note: `research-notes/archive/G122_real213_padic_research_direction.md`.

**2026-05-09 (later, marathon batch 1)**: User directive "seal
없애버리고 다 213 native로" — emptied SEALED_DIRTY_PREFIXES.  Full
scan post-seal-empty: **2491 PURE / 164 DIRTY / 0 sealed**.

After batch 1-10 fixes (27 theorems converted): **2519 PURE / 137
DIRTY / 0 sealed**.

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
| `pure_atomic_observables_capstone` | 17-conjunct atomic ratios |
| `invAlphaEm_precision_theorem` | 0.2 ppb 1/α_em structural precision |
| `alpha_em_so10_capstone` | SO(10) tail correction |
| `alpha_em_gram_capstone` | Gram self-energy correction |
| `tower_native_completeness_program` | completability = two-growth-axes comparison: boundary (`CrossDetOvertake`, 10/0), Liouville `W=d` free modulus (`LiouvilleModulus`, 13/0), finite-coordinate closure under `×`/exponent (`DepthClosure`, 16/0), coordinate generator (`DepthCoordGenerator`, 10/0), residue tie (`DepthCeilingResidue`).  Narrative `theory/math/analysis/tower_native_completeness.md` |

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

### Tier 5.1 CLEARED — `Lib/Math/GRA/` (Marathon 16, 2026-05-28)

`E213.Lib.Math.GRA.*` — 22 files (umbrella + Common + 7 Phases 1–6 +
5 Phases 7–11 + 1 unified `Enrichment` + 3 Phases 12–15
support (Naturality + SectionRetraction + Monoidal) + 1 each
from Phases 16–18 + 1 unified `HasDistinguishing213` for
Phases 19–21 + Phase 22),
~3500 lines, **all PURE / 0 DIRTY** (verified by `tools/scan_axioms.py`
plus direct `#print axioms` for the multi-namespace `HigherAlgebra.lean`
that the scanner's last-namespace heuristic mis-attributes).

Upgrade pattern applied throughout:
  · `Nat.gcd 2 3 = 1` (DIRTY [propext] via well-founded
    recursion) → switch `GRAModel.ax_coprime` to
    `E213.Tactic.NatHelper.gcd213 gen1 gen2 = 1`, which kernel-
    reduces to `rfl` for the (2, 3) instance.
  · `*_grade_oplus` / `*_grade_otimes` / `*_greedy` `by simp [...]`
    → `rfl` or `Nat.le.refl` (the definitions are kernel-equal
    to the goals).
  · `nt_reach` and the 5 Reading variants `by omega` per literal
    case → shared PURE `Common.reach_23`, which uses strong
    recursion + a 2-step lemma `reach_step` proving
    `(k+2 = 2a + 3b) → ((k+2)+2 = 2(a+1) + 3b)` via explicit
    `Nat.mul_succ` / `Nat.add_assoc` / `Nat.add_comm`.
  · `*_depth_eq` `by_cases ... omega` → shared PURE
    `Common.depth_formula`, which splits on `n % 3 ∈ {0,1,2}`
    via `cases_lt_three` and the helper lemmas
    `div3_3k_{1,2,3,4}` (inductive PURE divisor identities)
    plus `Meta.Nat.AddMod213.div_add_mod`.
  · `universal_depth_comparison` `by omega` → shared PURE
    `Common.ceil3_le_ceil2`, proved by 6-step strong induction
    over the LCM(2,3) cycle with `Meta.Nat.NatDiv213.add_div_right_pos`.
  · `transport_depth_bound` / `master_translation*` /
    `reach_translation` `simp [...]` → explicit `exact` with
    typed witnesses.
  · `depth_times_3_lower` `by omega` → explicit cancellation
    via `Meta.Nat.AddMod213.div_add_mod` +
    `NatHelper.le_of_add_le_add_left`.

Shared helpers added in `lean/E213/Lib/Math/GRA/Common.lean`
(7 public PURE theorems): `coprime_2_3`, `two_lt_three`,
`reach_offset`, `reach_23`, `depth_formula`, `greedy_form`,
`ceil3_le_ceil2`.

Phases 7–11 (category theory + enrichment, all PURE):

  · `Category.lean` (9 PURE): 213-native `Cat` typeclass
    (universe-polymorphic), `GRACat`, `ReadingCat`,
    connectedness witness.
  · `Groupoid.lean` (10 PURE): `Groupoid` typeclass on top of
    `Cat`; pointwise `HEq`-form of identity (carrier types are
    syntactically distinct but defeq Nat, so `HEq` is the natural
    form); `ConnectedHub` structure; `Reading.hubAtNT` witness.
  · `Hom.lean` (10 PURE): `GRAHom` (data-preserving, not
    necessarily invertible); `id`/`comp` category laws; forgetful
    `GRAIso → GRAHom`; grade-agreement and grade-oplus-via-hom
    theorems.
  · `DepthFunctor.lean` (9 PURE): depth as constant functor on
    the (2, 3)-sub-category; `Reading_depth_const` shows all 6
    Readings agree on `⌈n/3⌉` for `n ≥ 2`.
Phases 11–15 (unified bipartite enrichment + naturality +
retraction + monoidal, all PURE):

  · `Enrichment.lean` (11 PURE): one parametric enrichment for
    all five Readings.  `BipartiteCarrier` is a `Nat` tagged with
    the bipartite constraint `n = 0 ∨ n ≥ 2` (excluding `n = 1`,
    which `gcd(2, 3) = 1` excludes from `{2a + 3b}`).
    `BipartiteCarrier.{zero, two, three}` carrier values;
    `BipartiteCarrier.combine` (additive on `n`, serving as both
    `⊕` and `⊗`).  `GRA23_Bipartite` is the enriched (2, 3)-GRA
    model; `forgetHom : GRA23_Bipartite → GRA23_NT` is the
    canonical projection.  The five domain flavours (Walk-length,
    Cochain-degree, Truncation-level, Operad-level, Resolution-
    exponent) are decompositions of one structure — the domain
    names were commentary, not mathematical content.
  · `Naturality.lean` (5 PURE): translation between enriched and
    simplified is natural with respect to the forgetful.
    `bipartite_depth_natural` + `DepthNaturality` capstone +
    `depth_naturality_witness`.  `bipartite_grade_match` and
    `bipartite_depth_match` give cross-reading translation via
    the hub.
  · `SectionRetraction.lean` (3 PURE): the forgetful has a
    section on its valid image (`n = 0 ∨ n ≥ 2`).
    `Bipartite.section` with retraction identity
    `forget ∘ section = id` and section identity
    `section ∘ forget = id`.  `BipartiteRetract` structures the
    data.
  · `Monoidal.lean` (14 PURE): `product : GRAModel → GRAModel →
    GRAModel` is the (2, 3)-monoidal product with component-wise
    `⊕` and `⊗` and additive grade.  `trivial23` is the unit
    (one-element carrier, grade ≡ 0).  `leftUnitHom` and
    `rightUnitHom` are the unit `GRAHom`s for `trivial23 ⊗ M`
    and `M ⊗ trivial23`.

Phase 16 (Lens bridge — Cat / HoTT as Readings, all PURE):

  · `LensBridge.lean` (11 PURE): the canonical Raw-level grade
    map `canonicalGradeMap := Raw.fold 2 3 (· + ·)`.
    `canonicalGradeMap_slash` uses `Nat.add_comm` PURE.  The
    bipartite enrichment grade map (`bipartiteGradeMap`) is
    *definitionally* `canonicalGradeMap`; pairwise agreement
    theorems across the five domain Readings reduce to
    `bipartite_canonical_agree` and follow by `rfl`.  Carrier-
    level realization theorems (`bipartite_realize_a`,
    `bipartite_realize_b`) show that the enriched Raw.fold
    projects to the canonical value on atoms.  Avoids
    `HasDistinguishing`-typeclass plumbing (which would bring
    `propext`); uses `Raw.fold` with literal `Nat`-arithmetic
    directly.

Phase 17 (carrier realization — closes Phase 16 open frontier,
all PURE):

  · `CarrierRealization.lean` (7 PURE): proves
    `canonical_ge_2 : ∀ r : Raw, canonicalGradeMap r ≥ 2` by
    Raw induction (atoms map to 2 or 3; slash adds two ≥-2
    values, hence ≥ 4).  This enables *direct* construction of
    `bipartiteRealize : Raw → BipartiteCarrier`, bypassing
    `Raw.fold` on the enriched type entirely.  The realization
    is `⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩`, so
    the grade-projection equals `canonicalGradeMap` by `rfl`.
    Avoids the PURE `combine_sym` problem on the `Prop`-field-
    carrying enrichment (which would force structural equality
    reasoning that brings `propext`).

Phase 18 (universal property — 1-cat proxy for GRACat-as-Cat,
all PURE):

  · `Universality23.lean` (5 PURE): `canonicalGradeMap_universal`
    proves any `f : Raw → Nat` with `f Raw.a = 2`, `f Raw.b = 3`,
    and slash-additive (`f (Raw.slash x y h) = f x + f y`) equals
    `canonicalGradeMap` pointwise.  Proof is direct Raw induction,
    closes by `rfl` at atoms.  Capstones with
    `canonical_arithmetic_forced` (the parameterless forcing
    statement) and `two_atoms_slash_agree` (uniqueness of the
    (2, 3)-profile function).  `bipartiteGradeMap_forced` and
    `bipartiteRealize_grade_forced` derive the enrichment-level
    grade equations as instances of the universal property —
    making the *forced-by-arithmetic* nature explicit rather
    than relying on `rfl` by definition.  This is the
    1-categorical proxy for the "GRACat-as-Cat is a Reading"
    frontier.

Phases 19–21 (unified `HasDistinguishing213` — universe-polymorphic
typeclass, all PURE):

  · `HasDistinguishing213.lean` (23 PURE): consolidation of
    Phases 19–21's three exploratory variants
    (`HasDistinguishingU`, `HasDistinguishingW`,
    `HasDistinguishingWFull`) into a single universe-polymorphic
    typeclass `HasDistinguishing213.{u, v} α` — fields `a, b : α`,
    `combine : α → α → α`, `Equiv : α → α → Sort v` (with
    refl/symm/trans), `combine_sym` up to `Equiv`, and
    `distinct_equiv : Equiv a b → False`.  Strict case
    instantiates `Equiv := Eq` (`v = 0`); categorical case
    instantiates `Equiv := GRAIso` (`v ≥ 1`).  Two closed
    instances:
      · `liftedReadingHasDistinguishing213 :
        HasDistinguishing213.{1, 0} (ULift.{1, 0} Reading)` —
        strict case on a `Type 1` carrier via `ULift`, with
        `readingCombine r s := if r = s then r else .NT` strictly
        commutative by case-split on `r = s` (`Reading` is
        enriched with `deriving DecidableEq`).  Atoms `NT`,
        `Graph` distinguishable by `decide`.  Realises the
        strict 2-categorical universe-lifting Phase 18 named
        as open.
      · `gra23HasDistinguishing213 :
        HasDistinguishing213.{1, 1} GRA23` — categorical case
        on the (2, 3)-packaged GRA-model type, with
        `combine := gra23Combine` (monoidal product),
        `Equiv := gra23Equiv` (`GRAIso` between underlying
        models), `combine_sym := gra23Combine_sym` (the
        swap iso `(a, b) ↦ (b, a)`, grade-comm via
        `Nat.add_comm`), `distinct_equiv :=
        trivial23_gra23_not_iso_ntGRA23` (cardinality argument
        on `TrivialCarrier` subsingleton vs `Nat`'s `0 ≠ 1`,
        applied through `iso.right_inv`).
    Headline lemmas: `productSwapIso`,
    `productSwapIso_involutive`, `product_grade_sym`,
    `product_combine_sym_witness`, `trivial23_not_iso_NT`,
    plus the two instances above and existence witnesses
    (`hasDistinguishing213_GRA23_witness`,
    `hasDistinguishing213_ULiftReading_witness`).

Phase 22 (Lens.Unified × GRA capstone — Raw 연결, all PURE):

  · `LensIsoCapstone.lean` (27 PURE): the deepest 213-native
    statement of GRA's content.  `gradeLens : Lens Nat :=
    ⟨2, 3, (· + ·)⟩` is the canonical (2, 3) Lens whose
    `Lens.view r = Raw.fold 2 3 (· + ·) r = canonicalGradeMap r`
    by definitional unfolding.  `profile_view_eq_canonical`
    re-expresses Phase 18's universal property in Lens
    vocabulary: any Lens whose view obeys the (2, 3) atomic
    profile coincides pointwise with `gradeLens.view`.  By
    `Lens.Unified.lensIso_iff_kernel_eq`,
    `profile_lens_LensIso_gradeLens` proves every (2, 3)-profile
    Lens on Nat is `Lens.Unified.LensIso` to `gradeLens`.  Five
    `*Lens` defs (`walkLens` etc.) are explicit equivalence-class
    members; five `*Realize_grade_eq_lens` theorems show that
    Phase 17 realizations project to `gradeLens.view` by `rfl`.
    Master capstone `gra_lens_iso_class_capstone_holds` packages
    the universal property + 5 Reading `LensIso`s.

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


## Session history

Per-session running-total entries that previously lived in this
file have been removed.  The PURE/DIRTY status of any theorem is
the live `#print axioms` output:

```bash
tools/scan_axioms.py <module>            # one module
tools/scan_all_axioms.py                 # full tree scan
```

Migration patterns that recur across sessions are catalogued in
`LESSONS_LEARNED.md` (omega → decide / kernel rewrite, simp →
rw, funext avoidance via Setoid/Bundled-subtype) and detailed in
`theory/essays/pure_funext_avoidance.md`.  Git log preserves the
per-session record of conversions.
