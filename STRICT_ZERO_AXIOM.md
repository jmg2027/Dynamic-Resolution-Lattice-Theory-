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

  · The 213-mathematical core is ∅-axiom.  The only non-sealed `propext`/`Quot.sound`
    that remains is the **`Prop`-atom thesis surface**
    (`propAsDistinguishing*` / `canonical*Map` / `BoolProp.universalMorphism_commute_*`,
    category (a) — `propext` IS "`Prop` is an atom of meaning").  The **CayleyDickson
    category-D backlog is closed** (2026-06-01): `Trig.conj_mul_anti` via the
    `NonAssocStarRing213 Sedenion` bridge (`SedenionAlgebra213`), and
    `SedenionHeavy.flexible` via the `CDDoubleFlexible` cross-pair +
    `FlexAlt213 Cayley` — both verified PURE (`#print axioms`).  The Lens ring is
    **0 real DIRTY** (`scan_all_axioms.py --filter Lens`): its equivalence surface is
    stated on reading-equivalence (`ReadingEq.same` / `equivR` / `sameLens`), not `=` of
    views.  Run `tools/scan_all_axioms.py` for the live count.
  · **No `Classical.choice` and no `Lean.ofReduceBool` (`native_decide`) in any
    213-mathematical content** — the falsifiability-forbidden axioms are absent.
    The only `Classical.choice` carriers are three `CommandElab` elaborators
    (`Lib.Math.Tactic.QuadExtension`, `Meta.Tactic.{DeriveConjugationCodomain,
    VerifyConjugation}`), inherited via the `Lean.Elab.Command` monad — sealed
    plumbing per category (a), not math content.
  · The remaining real DIRTY are **`propext` / `Quot.sound` only** (the
    "allowed-but-not-target" core-kernel axioms) — the `Prop`-atom thesis surface
    (category B).  The CayleyDickson category-D items (`Trig.conj_mul_anti`,
    `SedenionHeavy.flexible`) are now both closed.  The category-D backlog uses the `Mobius213.Px` playbook
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

### Invert universal property + deep-research additions (2026-06-03)

`E213.Lens.Number.FoundingDialUnification` — **4 PURE / 0 DIRTY**.  The number-tower founding
meets the concurrent non-holonomicity discriminant-dial marathon at one order-2 companion
`comp p q`, split along its two coordinates: `founding_unit_floors_dial_trace_runs_tiers` — the
founding unit `q = NS − NT` is the dial's fixed determinant (`det (comp p q) = q`); the trace `p`
runs the discriminant (`disc = p² − 4q`); the forced atomic counts are the tier boundaries —
`p = 0` elliptic (founding swap `S`), `p = NT` parabolic (`disc = 0`), `p = NS` hyperbolic (golden,
`disc = NS² − 4 = NS + NT = d`).  (Det-floor + trace-dial parametric; `p = NT`/`p = NS` landing on
the tiers is atomic — pins `NS = 3`.)  And `parabolic_at_NT_is_difference_lens_depth1` — the
parabolic tier (trace `NT`) is the **difference-Lens rung**: `liftKZ 1 s n = s(n+1) − s n` is the
`ℤ`-difference, and parabolic ⟺ that output is constant (`polyDepthZ 1`, depth-1).  And
`hyperbolic_at_NS_is_ratio_cauchy_rung` — the hyperbolic tier (trace `NS`, det = unit `NS−NT`,
disc = `d`) is the ratio/Cauchy rung: the convergents' cross-det is the *same* unit
(`convergent_lowest_terms_is_det`), completing to `φ` (`phiCauchy_limit_eq_phiCut`).  So the
founding number-rungs *are* the tiers: `ℤ`-sign = elliptic, `ℤ`-difference (depth-1) = parabolic,
`ℚ`/`ℝ` ratio/Cauchy = hyperbolic.  And `count_constants_are_difference_fixed_below_parabolic` —
`ℕ` (count, depth-0 constants) is the difference-Lens **fixed locus** (`liftKZ 1 (const) = 0`),
sitting at the bottom of the parabolic (depth-1) tier.  So *every* founding rung is placed on the
dial: `ℕ` difference-fixed bottom of parabolic, `ℤ`-difference full parabolic, `ℤ`-sign elliptic,
`ℚ`/`ℝ` hyperbolic.  Builds on `FoundingDynamicBridge`.

`E213.Lens.Number.Nat213.Tower.PairCompletionUniversal` — **19 PURE / 0 DIRTY**.  The invert
move's **complete universal property** (existence ∧ uniqueness), Quot-free and choice-free,
**validated concretely**: `intTarget` (`Int` as an `AbTarget` from the PURE `Int213` kit),
`natToInt_hom`, `liftZ`, and `addCCS_completion_is_Int` — the additive completion of
`(Nat213, +)` is `ℤ` (`liftZ` is the integer-difference map; `(2,1) ↦ +1`, `(1,2) ↦ −1`), and by
the capstone it is the unique factoring hom.  The universal property is non-vacuous.
`AbTarget` (abelian-group target, laws as ∀-equalities); `lift M H f (a,b) = f a − f b`;
existence — `lift_respects_pairEquiv` (well-defined on the completion), `lift_combine`
(homomorphism), `lift_eta` (factors `f` through `η m = (m∘a,a)`); uniqueness — `lift_unique`
(any `g` respecting `pairEquiv` + `combine` + `η` equals `lift`), via `pair_equiv_eta_combine`
(every pair `~ η(a) ∘ inv(η(b))`); capstones `invert_factors_through_any_group` and
`invert_is_the_universal_group_completion`.  Group-algebra toolkit `ab_neg_add`,
`ab_add_add_add_comm`, `ab_add_{left,right}_cancel`, `ab_neg_unique`.  Makes "invert is one
move" precise: the invert move is *the* universal group completion, unique up to iso (initiality,
not an imported adjunction).

`E213.Lens.Number.Nat213.Tower.PairCompletion` — **+2 PURE (17 total)**.
`diagonal_is_combine_identity` (the emergent diagonal *is* the `combine`-identity, unit-free —
the no-exterior principle in a readout) and `invert_branch_two_distinct_instances`
(`ℤ ⊥ ℚ_+`: `add 1 1 ≠ mul 1 1`, two instances of one move joined at the diagonal).

`E213.Lib.Math.CassiniUnimodular` — **+2 PURE (13 total)**.  `qpow_one` and
`multiplier_unit_magnitude_sign_order_NT`: the unimodular multiplier `q = ±1` factors as (unit
magnitude `qpow 1 n = 1`, order-`NT` sign `qpow (−1) NT = 1 ∧ qpow (−1) 1 ≠ 1`) — the genuine
`(unit, period) = (1, NT)` factorization (the arithmetic re-readings of `NS = NT+1` are
numerology).

### Number-tower founding + invert-move addition (2026-06-03)

`E213.Lens.Number.SharedUnitAcrossReadings` — **1 PURE / 0 DIRTY**.  The honest unification
of the axis-readings: `the_unit_is_one_across_readings` — the unit `1` is one value across
count-difference (`NS − NT`, `ns_minus_nt_is_one`), the Möbius/ratio determinant
(`mobius_det_eq_ns_minus_nt`, `mobius_det_is_unit`), the Cassini oscillation
(`toggle_det_unit`), and the reciprocal law (`qpair_mul_swap_eq_qOne`).  Identity-of-the-unit
(downward), not an operator monoid (which has no shared carrier).

`E213.Lens.Number.Nat213.Tower.PairCompletion` — **15 PURE / 0 DIRTY**.  Includes
`swap_order_eq_NT` (the swap's order is exactly `NT = 2`: involution + non-identity, so
period-2 is forced by the count, not chosen — no period-`k` on a pair).  The **invert
move as one theorem**: a generic `CommCancelSemigroup` on `Nat213` (op + comm + assoc +
right-cancel, **no unit**) with pair-completion `pairEquiv M p q := M.op p.1 q.2 =
M.op p.2 q.1`, equivalence-relation proofs (`pairEquiv_{refl,symm,trans}`), the `swap`
involution, and `combine`.  `combine_swap_equiv_diagonal` — `x ∘ inv(x)` lands on the
diagonal, so the completed group's identity **emerges** as the diagonal class, unit-free
(forced: `Nat213` has no additive `0`, yet its additive completion has an identity).
Instances `addCCS` (`op=+` → ℤ model) and `mulCCS` (`op=·` → ℚ_+); `mulCCS_recovers_qpairEquiv`
(`Iff.rfl`) recovers `NatPairToQPos.qpairEquiv`; capstone `invert_is_one_move`.  ℤ and ℚ_+
are one construction read on the two operations.

`E213.Lens.Number.Nat213.Order` — **8 PURE / 0 DIRTY**.  Native strict order
`lt a b := ∃ c, add a c = b` (no Lean `Nat` order — `Nat.lt_or_ge` / `Nat.le_antisymm` /
`Nat.mul_lt_mul_right` all pull `propext` + `Classical.choice` + `Quot.sound`).
`add_ne_self`, `lt_irrefl`, `lt_ne`, `succ_lt_succ_of_lt`, `lt_trichotomy` (structural
double recursion), `lt_mul_self` (strict square-monotonicity, **purely from
distributivity** — no order lemma), and the payoff `mul_self_inj` (`a·a = b·b → a = b`).

`E213.Lens.Number.Nat213.Tower.NatPairToQPos` — **+8 PURE (19 total) / 0 DIRTY**.  The
**reciprocal involution**, multiplicative twin of `NatPairToInt`'s negation: `qSwap`
(period-2, `qSwap_involutive`), `qpair_mul_swap_eq_qOne` (`x·(1/x)=1`, the reciprocal law),
`qOne_reciprocal_fixed` (`1/1=1`), `qpair_diagonal_collapse` (diagonal ~ unit `1`),
`reciprocal_fixed_of_unit` + `reciprocal_fixed_iff_unit` (the *exact* fixed-point
characterization `qSwap p ~ p ↔ p ~ qOne`, full twin of `zero_unique_negation_fixed`, via
`Order.mul_self_inj`), and the bundle `reciprocal_is_multiplicative_twin_of_negation`.  One
swap, two folds, two units (`0` for `+`, `1` for `·`).

### Non-holonomicity finite-state escape + depth-monotone bridge + discriminant dial (2026-06-03)

The non-holonomicity / holonomicity-hierarchy thread, closed end to end (all **0 DIRTY**):

`E213.Meta.Int213.Order` — **34 PURE**.  The ∅-axiom `Int` ordering layer (Lean-core
`Int.le_trans` / `lt_trichotomy` carry `propext`), rebuilt from the inductive `Int.NonNeg` +
the `ring_intZ` reflection tactic: `le_trans` / `lt_trans` / `lt_of_le_of_lt` / `lt_of_lt_of_le`,
`lt_irrefl` (the contradiction engine), `le_of_lt`, `add_le_add_{left,right}`, the sign trichotomy
`pos_zero_or_neg`, negation-reverses-order (`lt_of_neg_lt_neg`, `neg_pos_of_neg`), and the `ofNat`
order embedding (`ofNat_le`, `le_of_ofNat_le`).  Reusable foundation.

`E213.Lib.Math.Cauchy.PolyDepthMonotone` — **11 PURE**.  `polyDepthZ_evMono`: every finite-Δ-depth
integer sequence is eventually monotone (non-decreasing or non-increasing).  LPO-free via the
constant-top-difference sign trichotomy — `c>0` ⟹ eventual strict increase (`posTop_evStrictMonoZ`,
the faithful-`Int` port of `positive_floor`'s descent + the eventual-positivity telescope
`evStrictMonoZ_eventually_pos`), `c<0` ⟹ negation (`liftKZ_negS_apply`, pointwise to dodge
`funext`'s `Quot.sound`), `c=0` ⟹ genuine depth-drop (faithful `Int` difference — the branch the
`ℕ` truncated version could not close).

`E213.Lib.Math.Cauchy.ThueMorseRingEscape` — **4 PURE**.  `s2Z_not_polyDepthZ`: the binary digit-sum
(popcount) has no finite difference-depth (`MonoFromZ` contradicts `s2_not_eventually_monotone`,
`AntiFromZ` ⟹ bounded ⟹ contradicts `s2_unbounded` via `s2 (ones k) = k`).

`E213.Lib.Math.Cauchy.DepthMonotoneSynthesis` — **2 PURE**.  Joins the algebraic and order-theoretic
readings of depth: `newtonZ_evMono` (every Newton polynomial is eventually monotone) and
`s2Z_not_polynomial` (popcount equals **no** polynomial `newtonZ c d`, the ring-escape read through
`DepthCharacterization.finite_depthZ_iff`).

`E213.Lib.Math.Cauchy.HomogRecPeriodic` — **1 PURE**.  `evPeriodic_homogRec`: eventually periodic ⟹
`HomogRec` (the elementary half of the bounded-`HomogRec` characterization; order `k=p`, prefix
killed by an `if`-guarded `lead`/`R`).

`E213.Lib.Math.Cauchy.CFiniteHomogRec` — **3 PURE**.  C-finite ⊆ P-recursive: `order2_homogRec` /
`order3_homogRec` (a constant-coefficient recurrence *is* `HomogRec`), `trib_homogRec` (Tribonacci is
holonomic — the opposite pole from Thue–Morse).

`E213.Lib.Math.Cauchy.EllipticPeriodicTier` — **17 PURE**.  The order-2 companion discriminant as the
holonomicity-hierarchy dial: `comp_disc` (`disc (comp p q) = p²−4q` = the `HyperbolicEllipticTrace`
discriminant), `comp_eq_S` / `comp_eq_U` (the elliptic generators *are* the companions of the
periodic recurrences), the trichotomy — *elliptic* `periodic_elliptic_{S,U}` (periodic floor),
*parabolic* `parabolic_iff_depth1` (`disc=0` ⟺ linear depth-1, an iff), *hyperbolic*
`hyperbolic_strictMono` / `hyperbolic_grows` (strictly increasing, unbounded).  **The dial is
special to order 2 — it does not lift**: `cubic_disc` + `cubic_disc_witnesses` show `Δ₃`'s sign does
not classify periodicity (periodic `(0,0,1)` and growing Tribonacci `(1,1,1)` both `Δ₃<0`); the
order-3 periodicity dial is root-location (cyclotomic, `|c|=1`), witnessed by
`periodic_elliptic_order3_p4` / `periodic_elliptic_order3_p6`.

`E213.Lens.Number.FoundingDynamicBridge` — **1 PURE**.  `founding_swap_is_elliptic_floor`: the
number-tower founding's static invert-**swap** (= negation, period-2 by `NT`, `NatPairToInt.
swap_realizes_negation`) is the **elliptic floor** of the dynamic discriminant dial — `comp 0 1 = S`,
`Mat2.det (comp 0 1) = NS − NT` (floor determinant = the shared founding unit), `disc < 0`,
`S² = −I` (negation-of-identity), `zero_unique_negation_fixed`.  The static number-tower founding and
the dynamic non-holonomicity dial pinned as one structure (shared floor = unit `1`; shared ceiling =
the residue).

`E213.Lib.Math.CeilingSchema` — **5 PURE**.  The residue ceiling is **one phenomenon**, not five
engines: `ReachedByNoStage gen target := ∀ s, gen s ≠ target`, `not_surjective_of_reachedByNoStage`
(the schema *is* non-surjectivity), and `ceilings_are_nonsurjectivity` bundling the universal
diagonal (`diag_reached`, Cantor archetype `∀ f, ¬Surjective f`), the non-holonomicity escape
(`s2Z_poly_reached`, popcount = no `newtonZ c d`), and the foundational residue
(`object1_not_surjective`) as one shape — the finite-stage map missing its target.  Classically one
Cantor/cardinality argument; ∅-axiom forces named constructive witnesses (the "engines" are
realizers, the domains Lens-carvings).

`E213.Lib.Math.Cauchy.DetZeroCollapse` — **6 PURE**.  The determinant spectrum of the order-2
recurrence read on the Cassini / discrete-Wronskian `cas s n := s n · s(n+2) − s(n+1)²`:
`geometric_cas_zero` (order-1 ⟹ `cas ≡ 0`, the `det = 0` collapse — the orbit is a geometric ray,
one ratio value), `cas_step` (Abel–Liouville: `cas s (n+1) = q · cas s n`, so the Wronskian's
geometric ratio *is* the determinant `q`), `cas_conserved_unit` (`q = 1` ⟹ `cas` conserved) and
`cas_period2_neg_unit` (`q = −1` ⟹ `cas s (n+2) = cas s n`).  `det` is the quotient-space
characteristic value: `0` collapse, `±1` unit, `|q| ≥ 2` expansion.

`E213.Lib.Math.Cauchy.WronskianDepth` — **8 PURE**.  The unit's two faces have **opposite
additive-depth status**: `cas_unit_depth0` (`det = +1` ⟹ the conserved Wronskian is `polyDepthZ 0`,
additively trivial — the magnitude unit) and `cas_neg_unit_no_finite_depth` (`det = −1` with
`W₀ ≠ 0` ⟹ the period-2 sign-flipping Wronskian is **not eventually monotone**, so has **no finite
depth** — additively maximal, the sign unit), bundled in `unit_faces_opposite_depth`.  Support:
`int_ne_neg_self`, `cas_neg_unit_ne_zero`, `cas_neg_unit_consecutive_ne`,
`period2_nonconst_not_evMono`.  One multiplicative unit, two opposite additive readings (the §5.2
`NT = 2` sign carries the additive richness).

`E213.Lib.Math.Cauchy.GoldenPiFaces` — **3 PURE**.  φ and π named as the two unit faces:
`golden_companion_sign_face` (`comp 1 (-1)`, the Fibonacci companion `x²−x−1`, has `disc = 5 =
NS+NT` and `det = −1` — φ is the **sign face**), `golden_cassini_period2` (any golden orbit's
Cassini is period-2, the classical `F(n+2)F(n)−F(n+1)² = (−1)^{n+1}`), and
`golden_cassini_no_finite_depth` (with nonzero initial Cassini, φ's Cassini has no finite
difference-depth — additively maximal).  π is the `det = +1` magnitude (elliptic/rotation) face at
an irrational angle — the open pole where the periodic floor fails.

`E213.Lib.Math.Cauchy.ZeroInfinityHole` — **5 PURE**.  `0` and `∞` as **one hole, not two dual
values** — the single point where the reciprocal fold `x ↦ 1/x` returns no value, named twice (`0`
from inside the values, `∞` through the reciprocal).  `zero_no_reciprocal` (`q · 0 ≠ 1` — `0` is the
unique non-invertible point, the value-side name of `∞`), `self_reciprocal_iff_unit` (`q·q = 1 ↔ q =
±1`, via the PURE `Int213.int_sq_le_one` — the reciprocal-fixed core is exactly the units) and its
contrapositive `non_unit_not_self_reciprocal`, `cas_zero_collapses` (`det = 0` ⟹ the Casoratian
vanishes from the next step — the hole's value-image is the area crushed to `0`), bundled in
`zero_is_hole_units_are_core`.  Treating `0` as a value smuggles half of an `∞`-system: a
reciprocal-closed value-system admitting `0` is forced to admit `1/0`; the founding's `ℚ₊` excludes
both symmetrically (`qSwap` total, unique fixed point `1`).  Collapse at the hole, conservation on the
reciprocal-fixed core `±1`.

`E213.Lib.Math.MaxEntropy` — **8 PURE**.  Structurelessness as a **positive intrinsic property**.
`MaxEntropy s := ¬ ∃ d, polyDepthZ d s` — no finite holonomic certificate generates `s` (the
*incompressibility* / measure-free reading of maximum entropy; the measure reading would smuggle an
exterior ruler).  `maxEntropy_reachedByNoStage` / `maxEntropy_not_surjective` (a max-entropy
sequence forces the universal Newton generator `newtonGen` to be non-surjective — the ceiling's own
non-surjection, read as a property of `s` not of a tactic).  The proven escapes collected under the
one predicate: `thueMorse_maxEntropy` (the dense automatic popcount counter) and
`golden_cassini_maxEntropy` (the `det = −1` sign face), joined in `maxEntropy_two_faces`.  The
non-holonomic pole is not a blank left open but the *presence* of maximal genericity —
source-without-enclosure named in information terms; not stipulated (the residue's genericity is the
theorem `object1_not_surjective`, and a `MaxEntropy` sequence is its constructive realizer).

`E213.Lib.Math.DetSpectrumPoles` — **1 PURE**.  The capstone uniting the two ends of the
det-spectrum as the **two folds' non-values**: `det_spectrum_poles_and_center` — for an order-2 orbit
read on its Casoratian, `q = 0` collapses into the **multiplicative hole** (`cas s (n+1) = 0`,
`ZeroInfinityHole`); `q = −1` (nonzero seed) is the **additive ceiling** (`MaxEntropy (cas s)`, no
finite handle, `WronskianDepth`); and the magnitude unit `q = +1` (nonzero seed) is the
**doubly-finite center** — never `0` (away from the hole, via conservation) and `polyDepthZ 0` (away
from the ceiling).  The two degeneracies bracketing the live region are not unrelated pathologies but
the multiplicative fold's hole (`0`/`∞`) and the additive fold's ceiling (maximum entropy /
non-surjection) — the two non-values the number tower excludes; the unit is where a genuine
distinguishing survives.

`E213.Lens.Number.IntFoldForms` — **13 PURE**.  Realizes canon §6.9 (status-symmetric folds): ℤ's
own fold is negation `x ↦ −x`, and a fold is correct only if `0` and `∞` carry the same status (both
genuine carrier elements).  Plain ℤ is torsioned (`0` present, `∞` absent); there are exactly **two**
correct closures.  **One-point** `ℤ̂ = Option Int` with `∞ = −∞`: `negHat` is an involution
(`negHat_involutive`) whose fixed points are exactly `{0, ∞}` (`negHat_fixed_iff`) — both fixed
(`negHat_zero_and_inf_fixed`), the form reciprocal reads by *swapping* `0 ↔ ∞`.  **Two-point**
`ℤ̄ = IntBar` with `+∞ ≠ −∞`: `negBar` fixes only `0` (`negBar_fixed_iff`) and **swaps** `±∞`
(`negBar_zero_fixed_inf_swapped`).  In both the genuine integers `n ≠ 0` are proper 2-cycles `{n, −n}`
(`negHat_value_two_cycle`) — `0`/`∞` are the fold's symmetry centres, not stratum-values.  Bundled in
`int_correct_fold_forms`.  `neg_neg_int` / `neg_self_zero` (constructor-matched Int helpers, the
`int_ne_neg_self` pattern); literal `−0 = 0` closures by `decide`.

`E213.Lens.Number.FoldDuality` — **13 PURE**.  The two founding folds meet on the shared four-point
fixture `Q4 = {∞, 0, +1, −1}` (the reciprocal-closed core of `ℤ̂`) and are **exact mirror images**:
negation `negQ` **fixes** the 영무한대 pair `{0, ∞}` (`negQ_fixes_zeroInf`) and **swaps** the units
`{±1}` (`negQ_swaps_units`); reciprocal `recQ` **swaps** `{0, ∞}` (`recQ_swaps_zeroInf`) and **fixes**
`{±1}` (`recQ_fixes_units`).  Both involutions (`negQ_involutive`, `recQ_involutive`); fixed-point
characterizations `negQ_fixed_iff` (`= {0,∞}`) / `recQ_fixed_iff` (`= {±1}`); status-symmetry
predicates `BothFixed` / `Swapped`; capstone `two_folds_dual_on_pairs`.  Each ℤ/2 fold fixes the
two-element orbit the other swaps — the additive and multiplicative folds exchange the roles of the
hole pair and the unit pair (the sharpest "0 is to `+` as 1 is to `×`").  All by `rfl` / `decide`.

`E213.Lens.Number.FoldKlein` — **9 PURE**.  The two folds **generate a Klein four-group** on the
fixture.  Their composite `bothSwap := negQ ∘ recQ = recQ ∘ negQ` (the two folds **commute**,
`negQ_recQ_comm`) is the **third non-identity involution** — it **swaps both** orbits
(`bothSwap_swaps_both`) and so is **fixed-point-free** (`bothSwap_no_fixed`).  `klein_four_group`
bundles the full `ℤ/2 × ℤ/2` table (each involutive + the three pairwise products close among them);
`klein_fixed_orbit_profile` distinguishes the three non-identity elements by which orbit they fix —
`negQ` the hole pair `{0,∞}`, `recQ` the units `{±1}`, `bothSwap` neither.  The additive fold, the
multiplicative fold, and their antipode product exhaust the involutive symmetries of the hole/unit
fixture.  All by `rfl` / `decide`.

`E213.Lib.Math.Real213.FoldReflections` — **11 PURE**.  The matrix witness of `FoldKlein`: the two
folds are the integer matrices `N = [[−1,0],[0,1]]` (negation) and `R = [[0,1],[1,0]]` (reciprocal),
both **involutive reflections** (`N_involutive`, `R_involutive`; `N_det = R_det = −1`), and their
product is the founding elliptic swap `N · R = S` (`negation_recip_eq_swap`, `ModularElliptic.S`,
`det = +1` — two reflections compose to a rotation).  `S² = −I` (`S_sq_central`) — matrix order `4`
halving to projective order `2`; the folds commute only projectively (`recip_negation_eq_neg_swap`:
`R · N = −I · S`, differing by the central Cassini sign).  Capstone
`two_reflections_compose_to_founding_swap`.  All by `decide`.  Closes the cross-frame link
`FoldKlein` left narrative.

`E213.Lib.Math.Real213.EllipticCycleFixtures` — **7 PURE**.  The two elliptic generators of
`PSL(2,ℤ) = ℤ₂ * ℤ₃` as cyclic fixtures.  `S` (the folds' product, `FoldReflections`) has projective
order 2 (`S_proj_order_2`, `S² = −I`) — the 영무한대 swap.  `U = [[0,−1],[1,1]]` has projective
order 3 (`U_proj_order_3`, `U³ = −I`): its Möbius action `z ↦ −1/(z+1)` is a fixed-point-free
**3-cycle** `∞ ↦ 0 ↦ −1 ↦ ∞` on the Eisenstein fixture `{∞, 0, −1}` (`uCyc`, `uCyc_cube`,
`uCyc_no_fixed`, `uCyc_sq_no_fixed`).  Capstone `elliptic_generators_are_two_and_three`: projective
orders `2, 3` are the free factors of the modular group; the matrix orders `4, 6` reduce through the
central `−I`.  All by `rfl` / `decide`.

`E213.Lib.Math.Real213.HyperbolicBoost` — **11 PURE**.  The hyperbolic face of "product of two
reflections": the golden iterator `G = [[2,1],[1,1]]` (φ's Möbius map, `det = 1`) factors as
`A · B` (`golden_boost_eq`) with `A = [[1,0],[−1,−1]]`, `B = [[2,1],[−3,−2]]` both involutive
reflections (`A_involutive`, `B_involutive`; `A_det = B_det = −1`).  `G` is **hyperbolic**
(`G_hyperbolic`: `trace 3 > 2`, `disc = tr²−4 = 5 = NS+NT`, real eigenvalues, infinite order — no
periodic floor), the boost to the elliptic `S = N·R`'s rotation (`FoldReflections`).  Capstone
`two_reflections_compose_to_golden_boost`: every `SL(2,ℤ)` element is a product of two reflections;
`|trace|` against `2` selects rotation (elliptic, periodic) vs boost (hyperbolic, aperiodic) — the
same `tr²−4` dial.  All by `decide`.

`E213.Lib.Math.Real213.ParabolicTranslation` — **10 PURE**.  Completes the trichotomy's third face:
the parabolic translation `T = [[1,1],[0,1]]` (`det = 1`, `trace = 2`, `disc = 0`, `T_parabolic`)
factors as `Aₚ · Bₚ` (`parabolic_translation_eq`) with `Aₚ = [[1,0],[0,−1]]`, `Bₚ = [[1,1],[0,−1]]`
both involutive reflections in **parallel** mirrors.  Capstone `sl2_trichotomy_as_two_reflections`:
the whole `SL(2,ℤ)` order-2 trichotomy is one frame — product of two reflections — with `tr²−4`
selecting the face: elliptic `S = N·R` (`disc = −4`, rotation), parabolic `T = Aₚ·Bₚ` (`disc = 0`,
translation, the difference-Lens depth-1 rung), hyperbolic `G = A·B` (`disc = 5`, boost).  All by
`decide`.

`E213.Lib.Math.Real213.Mat2CayleyHamilton` — **4 PURE**.  The root of the dial:
`cayley_hamilton` — every `Mat2` satisfies `M² = tr(M)·M − det(M)·I` (`= charComb`), proved
**generally** by `ring_intZ` (not `decide`).  `char_poly_discriminant`: `disc = tr²−4·det` is the
discriminant of the characteristic quadratic `λ² − tr·λ + det`; `dial_is_char_discriminant` bundles
the two — Cayley–Hamilton is the primitive, the elliptic/parabolic/hyperbolic trichotomy is the sign
of its discriminant.  (`S²=−I`, `U²=U−I`, `T²=2T−I`, `G²=3G−I` are the `(tr,det)` specializations.)
Proved propext-free via `show` + entry `rw` (`Mat2.mk.injEq` / `simp` pulls `propext`).

Also extended this thread (already cataloged elsewhere): `Cauchy.ThueMorseAperiodic` (42 PURE — the
canonical dense witness, run-length ≤ 2, automatic structure `tm_eq_popParity`, dyadic
self-similarity, witness unification `isPow2_eq_s2_one`, the continued fraction `tmCF`) and
`Cauchy.MorseHedlund` (16 PURE — `bool_autoRec_iff_evPeriodic`).

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

`E213.Lib.Math.Cauchy.DepthAperyCubic` — **23 PURE / 0 DIRTY**.  The Apéry
zeta coefficient-degree statistic: the minimal-holonomic recurrence coefficients
of ζ(2) (`(n+1)²uₙ₊₁=(11n²+11n+3)uₙ+n²uₙ₋₁`, degree 2) and ζ(3)
(`n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂`, degree 3) are discrete polynomials whose
finite-difference depth equals their degree.  `zeta2_to_zeta3_degree_step`,
`apery_cubic_rung` (`aperyTop=n³`, `aperyLead=34n³−51n²+27n−5`, `aperyBot=(n−1)³` all
`polyDepth 3`, floors `6,204,6`), `zeta2_quadratic_rung` (floors `2,22,2`).  Exactness:
`aperyTop_depth_exact` / `zeta2Top_depth_exact` (`polyDepth d ∧ ¬ polyDepth (d−1)`).
ζ(3)'s cubic coefficients reindexed to `n=m+2` (all-positive); cubic/quadratic
difference identities discharged by the `Meta.Nat.PolyNat` reflection ring; lower bounds
by `decide`.  Degree is *incidental to irrationality* (ζ(4) order 2, Catalan β(2) open) —
ζ(3) degree 3 is the exception above the order-2 degree-2 Apéry-like family.

`E213.Lib.Math.Cauchy.DepthSelfReference` — **3 PURE / 0 DIRTY**.  The `diff` ladder
realises self-reference's Converge / Escape outcomes (`Lens.SelfReferenceThreeOutcomes`) on
`Nat` sequences: `floor_converges` (`W` `reachesFloor`, settles at the unit `1 = det P =
NS−NT`, the Lambek terminating descent) and `geom_escapes` (`2ᵏ` `¬ reachesFloor`, the
residue's top-less ascent), bundled in `diff_converge_or_escape`.  Naming capstone — no
operator forced across the Raw-peel vs `Nat`-`diff` types; parallel readings of the §5.2
self-pointing sharing the count-Lens unit `1`.

`E213.Lib.Math.Cauchy.DepthResidueFloor` — **2 PURE / 0 DIRTY**.  The self-pointing depth
ladder anchored at the residue floor: `diff` as a pointing event, depth as the count of
re-pointings to self-coincidence.  `floor_polyDepth0` (`P`/φ Cassini `W` is depth 0 — the
self-same rule that is its own fixed point) and `self_pointing_depth_ladder` (`polyDepth 0
W ∧ polyDepth 1 ratio ∧ polyDepth 2 zeta2Top ∧ polyDepth 3 aperyTop`): from the `P`/φ floor
the depth climbs by one degree of `n`-dependence per rung (e:1, ζ(2):2, ζ(3):3).  Reads the
divergence-depth count as drift-from-pure-self-reference, placing it inside the
residue/no-exterior canon (`DepthCeilingResidue` = infinite depth = residue).

`E213.Lib.Math.Cauchy.DepthQuadraticGeneric` — **7 PURE / 0 DIRTY**.  Every quadratic
discrete polynomial has divergence-depth 2: `quadratic_polyDepth` — `∀ A B C, polyDepth 2
(fun n => A·n²+B·n+C)` (floor `2A`), capping the whole order-2 degree-2 Apéry-like (Zagier
sporadic: ζ(2)-Apéry, Domb, Almkvist–Zudilin, Catalan-β(2), …) family in one statement.
Newton-form transfer `A·n²+B·n+C = newton (C,A+B,2A) 2` (via `binom n 1 = n`, `n² =
2·binom n 2 + n`) along the new reusable `polyDepth_congr` + `newton_polyDepth`; the one
nonlinear identity by the `Meta.Nat.PolyNat` reflection ring.  Dissolves the
multivariate-`Nat`-AC obstruction (no `ring`/`omega`).

`E213.Lib.Math.Cauchy.CasoratianSigned` — **17 PURE / 0 DIRTY**.  The *signed* Casoratian law
+ its signed telescope (incl. concrete `cube_casoratian_telescope`), sign carried 213-natively as a ℕ-pair
(`Lens.Number.Nat213.Tower.NatPairToInt`: integer = pair `(a,b)` = `a−b`, negation = axis
swap).  `casoratian_signed` — `npairEquiv (scale c₂ Cₙ) (scale c₀ (neg Cₙ₋₁))` *is*
`c₂Cₙ = −c₀Cₙ₋₁`, unfolding to `casoratian_step` verbatim — signed law ∅-axiom over ℕ, **no
`ℤ` type, no propext**.  Pair-congruences (`scale_mul/comm/congr`, `neg_congr`), `neg_neg`
(swap involution = period-2 Oscillate), `iterNeg` (accumulated sign, `iterNeg_succ_succ`
period 2).  **Signed telescopes**: `telescope_pair` — ζ(3) constant-sign shape `scale (∏ P)
Cₙ ~ scale (∏ Q) C₀` (`P=n³`, `Q=(n−1)³`: the `+6/n³` Casoratian); `telescope_pair_alt` —
ζ(2) alternating shape `scale (∏ P) Cₙ ~ iterNeg n (scale (∏ Q) C₀)` (`P=(n+1)²`, `Q=n²`: the
`±5/n²` Casoratian, sign `(−1)ⁿ`).  The signed `±5/n²`,`±6/n³` closed forms realized ∅-axiom
over ℕ-pairs (the sign = the residue's binary axis-distinguishing).  The Casoratian's
magnitude (Converge/Escape, `CasoratianStep.telescope`) and sign (Oscillate, `iterNeg`) are
the two non-trivial `SelfReferenceThreeOutcomes` readings of one object.

`E213.Lib.Math.Cauchy.CassiniSigned` — **2 PURE / 0 DIRTY**.  The residue floor's cross-determinant as the depth-0 signed Casoratian: the Fibonacci Cassini `fib(n+2)·fib(n) − fib(n+1)² = (−1)ⁿ⁺¹` in ℕ-pair form — `cassini_pair`: `npairEquiv (fib(n+2)·fib(n), fib(n+1)²) (iterNeg (n+1) (1,0))`, the unit pair `(1,0)` toggled `n+1` times.  Magnitude `1` (the `det P = 1` floor, Converge depth 0) with the sign carried entirely by the period-2 axis swap (Oscillate); `cassini_step` is the subtraction-free Fibonacci identity, the `c₂=c₀=1` floor instance of `casoratian_signed`.  ∅-axiom over ℕ — the floor's `±1` with its sign, no `ℤ`.

`E213.Lib.Math.Cauchy.DepthCubicGeneric` — **5 PURE / 0 DIRTY**.  Every cubic discrete polynomial has divergence-depth 3: `cubic_polyDepth` — `∀ A B C D, polyDepth 3 (A·n³+B·n²+C·n+D)` (cubic analog of `quadratic_polyDepth`, completing depth=degree to 3), via `cubic_eq` (cubic = `newton (D,A+B+C,6A+2B,6A) 3`) + `newton_polyDepth` + `polyDepth_congr`.  Crux `cube_eq` — `n³ = 6·binom n 3 + 6·binom n 2 + n` (the subtraction-free `n³ = 6·C(n,3)+6·C(n,2)+C(n,1)`, cube analog of `DepthQuadraticGeneric.sq_eq`), via the univariate `(n+1)³=n³+3n²+3n+1` (`poly_id`) + `sq_eq` + `cube_reorder` (the combine/reorder identity, PURE via `NatHelper.{add_mul,mul_assoc}` + `Nat.add_right_comm`, no propext-dirty `ring`/`ac_rfl`).  All multivariate reorders (the `cube_reorder` combine + the two collect steps in `cubic_eq`) are one-line `Meta.Nat.PolyNatM.poly_idM` calls.

`E213.Lib.Math.Cauchy.DepthCharacterization` — **13 PURE / 0 DIRTY**.  ★ The capstone of the divergence-depth thread: **finite divergence depth ⟺ polynomial**, over ℤ.  `finite_depthZ_iff` — `polyDepthZ d s ↔ ∃ c, ∀ n, s n = newtonZ c d n` (degree-≤d Newton form).  ⟹ is `NewtonGregory.reconstruct` (cⱼ=Δʲs0); ⟸ is `polyDepthZ_newtonZ` (Newton form has depth d), built on the new **ℤ binom-column depth** `polyDepthZ_binomColZ` (`polyDepthZ k (C(·,k):ℤ)`) via the ℤ-Pascal difference `diffZ_binomColZ` (`Δ C(·,k+1)=C(·,k)`) + the finite-depth ring (`polyDepthZ_add/smul`, `polyDepthZ_mono`).  Unifies the ℕ depth ladder ⊕ the concurrent-session ℤ reconstruct into one equivalence.  **Exactness** (`newtonZ_depth_drop`): a degree-`(e+1)` Newton form drops to depth `e` iff its top coefficient `c_{e+1}=0` — via `liftKZ_newtonZ_const` (`Δ^d(Newton form)=c_d`, from the shift `diffZ_newtonZ`).  So divergence depth = degree *exactly*.

`E213.Lib.Math.Cauchy.PolynomialDepth` — **13 PURE / 0 DIRTY**.  Every degree-`d` polynomial sequence has divergence-depth `d`, general: `polyDepthZ_polySeq` — `∀ a d, polyDepthZ d (polySeq a d)` where `polySeq a d n = Σ_{i≤d} aᵢ·nⁱ` (any `ℤ`-coefficients).  Via the finite-depth **ring** (`FiniteDepthAlgebra.polyDepthZ_{add,smul,mul}`): `idZ` (n↦n) depth 1 (`diffZ_id`, PURE Int213 `add_assoc`/`add_neg_cancel`), `powSeq i` (n↦nⁱ) depth `i` (`polyDepthZ_mul` ×`i`), `polyDepthZ_mono` lifts, `polyDepthZ_add` sums.  Subsumes the quadratic/cubic rungs in one — no Stirling, no per-degree reorder; the ring does the bookkeeping.  Unifies the ℕ depth ladder (`DepthAperyCubic` etc.) with the concurrent ℤ finite-depth ring.  `aperyLeadZ_depth` (instance): the ζ(3) Apéry leading coefficient `34n³−51n²+27n−5` (negative coeffs) has depth 3 over ℤ with **no reindex** (the ℕ `DepthAperyCubic.aperyLead` needed `n=m+2`); `aperyLeadZ_value` checks it `= 117` at `n=2`.

`E213.Lib.Math.Cauchy.OrbitDimension` — **32 PURE / 0 DIRTY**.  The C-finite rung strictly above the polynomials, the first step on the orbit-dimension ladder past `DepthCharacterization.finite_depthZ_iff`.  The divergence-depth axis is coarse above the polynomials (it bins `2ⁿ`, `e`'s value sequence, Fibonacci, Liouville all at `∞`); the **orbit dimension** of `⟨s, Δs, Δ²s, …⟩` separates them.  ★ `twoPow_is_diffZ_fixed` — the geometric **eigen-identity** `Δ(2ⁿ)=2ⁿ` (`2·2ⁿ−2ⁿ=2ⁿ`, via `ring_intZ` over the core-free `powInt`); `liftKZ_twoPow_fixed` — every iterate fixes it, the orbit is the single line `⟨2ⁿ⟩`.  `CFiniteZ s := ∃ k c, ∀ n, Δᵏs n = Σ_{i<k} cᵢ·Δⁱs n` (a monic constant-coefficient `Δ`-orbit recurrence; finite orbit dimension).  ★ `polyDepthZ_cfiniteZ` — **polynomial ⟹ C-finite** (zero lower part, annihilator `Δ^{d+1}`).  ★ `cfiniteZ_twoPow` — **`2ⁿ` is C-finite** (annihilator `Δ−1`, orbit dim 1).  ★★★ `twoPow_not_polyDepthZ` — **`2ⁿ` is not a polynomial** (`Δᵏ(2ⁿ)=2ⁿ`, never `≡0` since `2⁰=1≠0` via `Int.ofNat.inj`+`Nat.noConfusion`), the **strict inclusion** `polynomial ⊊ C-finite`.  `cfiniteZ_smul` / `cfiniteZ_shift` — C-finite is a module, shift-stable (same annihilator); `cfiniteZ_add_sameRec` — closed under `+` of two sequences sharing one annihilator (general `+` closure is `CFiniteRing.cfiniteZ_add`).  **The general geometric family** `geomZ c = cⁿ`: `geom_diffZ` (`Δ(cⁿ)=(c−1)·cⁿ`), `liftKZ_geomZ` (`Δᵏ(cⁿ)=(c−1)ᵏ·cⁿ`), `cfiniteZ_geom` (every geometric sequence is C-finite, orbit dim 1, annihilator `Δ−(c−1)`), `geom_not_polyDepthZ` (`c≠1 ⟹` not polynomial, via `powInt_eq_zero`: `xᵏ⁺¹=0⟹x=0`).  **Fibonacci** `fibZ`: `cfiniteZ_fib` — `fibZ` is C-finite with **orbit dimension 2** (`Δ²f=f−Δf` from `E²−E−I=Δ²+Δ−I`), the cleanest non-geometric, non-polynomial witness.  **Abelian-group structure**: `cfiniteZ_congr` (respects pointwise eq), `cfiniteZ_zero`, `cfiniteZ_neg` (`−s=(−1)·s`); `cfiniteZ_geom_mul` (`cⁿ·dⁿ=(cd)ⁿ`, the geometric Hadamard instance, orbit dims multiply `1·1=1`).  **Conserved unit**: `cassini_fibZ_step`/`cassini_fibZ_zero` — the Fibonacci Cassini cross-determinant `Cₙ=fibₙfibₙ₊₂−fibₙ₊₁²` oscillates `Cₙ₊₁=−Cₙ` (period-2), the conserved unit `±1` (= `det Qⁿ` = the number-tower's shared unit `det P=NS−NT=1`, the period-2 flip being the count-Lens negation).

`E213.Lib.Math.Cauchy.CFiniteRing` — **82 PURE / 0 DIRTY**.  The **difference-operator algebra** and the **C-finite ring closure under `+`**.  `applyOp p s = Σ_i pᵢ·Δⁱs` (coefficient list low-to-high `Δ`-power); linearity (`applyOp_add`/`applyOp_smul`), `Δ`-commutation (`applyOp_diffZ`), and ★★★ `applyOp_comm` (`p(Δ)q(Δ)s = q(Δ)p(Δ)s` — difference operators commute).  `conv` (coefficient convolution = operator product) with `applyOp_conv` (`(p·q)(Δ) = p(Δ)∘q(Δ)`).  ★★★ **the ring law** `conv_annih_add`: if `p` annihilates `s` and `q` annihilates `t`, the product `conv p q` annihilates `s+t` — the constant-coefficient annihilators *multiply* (orbit dimensions add).  **Bridge** (both directions): `cfiniteZ_to_annih` (`CFiniteZ s ⟹ ∃ monic `opOf`-operator annihilating `s`, via `applyOp_opOf` evaluating `Δᵏ−ΣcᵢΔⁱ` and `opOf_getLastD` proving leading `1`) + `annih_snoc_to_cfiniteZ` (a monic `lo++[1]` annihilator *is* the orbit recurrence `Δ^{|lo|}s=ΣcᵢΔⁱs`, via `applyOp_snoc_one` + `applyOp_eq_linComb`).  So **C-finite ⟺ has a monic constant-coefficient annihilator** — the orbit-recurrence definition coincides with the standard annihilating-polynomial one.  ★★★ **the capstone** `cfiniteZ_add`: `CFiniteZ s → CFiniteZ t → CFiniteZ (s+t)` — the monic annihilators multiply (`conv_snoc`: leading coefficients multiply, `1·1=1`; `+0`/`*1` syntactic noise absorbed by an existential-value `conv_snoc`), so `polynomial ⊊ C-finite` is a genuine **ring** under `+`, with the `conv`-monic toolkit `length_snoc`/`smulL_snoc`/`addL_snoc_right`/`length_addL_right_ge`/`opOf_snoc` (all `Nat.max`-free).  `cfiniteZ_one_add_twoPow`: `1+2ⁿ` is C-finite, a concrete sequence `+` generates that is neither polynomial nor geometric.  `cfiniteZ_sub` (with `OrbitDimension`'s `cfiniteZ_zero`/`cfiniteZ_neg`) completes the **abelian group under `±`**.  **§8 the shift as a difference operator** (toward C-D): `applyOp_shift` (`applyOp [1,1] = E`, the forward shift *is* `I+Δ`), `ePow k` (= `[1,1]` convolved `k` times = `Eᵏ`), `applyOp_ePow` (`applyOp (ePow k) s n = s(n+k)` — the `k`-shift is a polynomial in `Δ`).  So a monic shift recurrence is a monic `Δ`-annihilator.  **§9 C-D reverse direction** `cfiniteZ_of_shiftRec`: a sequence satisfying a monic order-`k` shift recurrence `s(n+k)=Σ_{i<k} bᵢ s(n+i)` (`ShiftRecZ`) is C-finite (`Δ`-orbit dim ≤ k) — via `eCombo` (shift→`Δ` operator `Σ bᵢ ePow i`, no binomial sums), `ePow_eq_snoc` (`ePow k` monic degree k), `eCombo_length_le`, `addL_snoc_right`.  So the standard constant-recursive definition ⟹ the `Δ`-orbit-recurrence one; `cfiniteZ_fib_via_shift` validates it end-to-end (Fibonacci's shift recurrence ⟹ `CFiniteZ fibZ`).  **§10–§11 C-D forward** — the dual shift-operator algebra `applyShift` (`Δ = applyShift [-1,1] = E−I` via `applyShift_diffBase`; `Δᵏ` as a shift operator `applyShift_dPow`; conv = composition `applyShift_conv`), `sCombo`/`dPow_eq_snoc`, and `shiftRec_of_cfiniteZ` (`CFiniteZ ⟹ ∃ monic shift recurrence`, the exact mirror of the reverse, no binomial sums).  ★★★ `cfiniteZ_iff_shiftRec`: **`CFiniteZ s ↔ ∃ K b, ShiftRecZ K b s`** — the full **"orbit dimension = recurrence order"** equivalence; `CFiniteZ` is exactly the standard constant-recursive class.  **§12 Hadamard, geometric factor** `cfiniteZ_geomScale`: `cⁿ·s` is C-finite for every C-finite `s` (a geometric weight rescales the shift coefficients `aᵢ↦aᵢ·c^{k−i}`, via `cfiniteZ_iff_shiftRec` + `geom_shiftSum`), generalizing `cfiniteZ_geom_mul` to `cⁿ·(n²)`, `cⁿ·fib`, ….  **§13 Hadamard, explicit-spectrum factor** `cfiniteZ_geomCombo_mul`: `(Σ aᵢcᵢⁿ)·t` is C-finite for every C-finite `t` (`geomCombo` = explicit `ℤ`-combination of geometrics; via `cfiniteZ_geomScale`+`cfiniteZ_add`, no determinant) — covers `(2·3ⁿ−5·2ⁿ)·fib`, `(3ⁿ+5ⁿ)·n²`.  (The *general* product `s·t`, both factors non-split, needs the monic resultant = `det(zI−M)`; determinant-free routes give only non-monic relations — the open frontier, C-B-adjacent.)

`E213.Lib.Math.Linalg213.DetN` — **19 PURE / 0 DIRTY**.  The general `n×n` **determinant over `ℤ`** (first-row cofactor / Laplace expansion), the foundational gap for the C-finite **Hadamard product** (monic annihilator = resultant = a determinant) and the **Casoratian rank**.  A matrix is `M : Nat → Nat → Int`; `det (n+1) M = Σⱼ (−1)ʲ·M 0 j·det n (minor M j)`, base `det 0 _ = 1` (`altSign`, `minor`, `cofSum`, `det`; sanity `det_one`, `det_two`).  ★ `det_congr` — `det` respects **pointwise** matrix equality (the ∅-axiom matrix-work pattern: `funext` is `Quot.sound`-dirty, so all matrix-as-function reasoning goes through pointwise congruence).  **§2 multilinearity in the first row**: `setRow0`, `detMinor_setRow0` (cofactor is row-0-independent), ★ `det_row0_add`/`det_row0_smul` (`det` is a linear functional of row 0).  **§3 the column-skip commutation** (the geometric core of the alternating property): `colShift j l = if l<j then l else l+1` (factored from `minor`), `colShift_lt`/`colShift_ge`, ★ `colShift_comm` (`a≤c ⟹ colShift a ∘ colShift c = colShift (c+1) ∘ colShift a` — deleting two columns in either order is the same; ∅-axiom via `Nat.lt_or_ge` case-splits, no propext), and `detMinorMinor_comm` (lifts it to the double minor's `det`, pointwise via `det_congr`).  (The full alternating property — two equal rows ⟹ `det=0` — reduces to one base case "top two rows equal ⟹ 0" whose per-term inputs are `colShift_comm`/`detMinorMinor_comm`; the remaining build is a nested-sum sign-reversing-involution ⟹ 0 lemma.  See `research-notes/G185`.)

`E213.Lib.Math.Linalg213.FibCassiniDet` — **3 PURE / 0 DIRTY**.  The bridge closing the loop between the determinant program and the C-finite orbit theory it serves.  `fibCas n i j = fibZ (n+i+j)` (the `2×2` Fibonacci Casoratian = companion power `Qⁿ` window); `cassini_fibZ_eq_altSign` (the Cassini cross-determinant in closed form `fibₙ·fibₙ₊₂−fibₙ₊₁² = altSign(n+1) = (−1)ⁿ⁺¹`, via `cassini_fibZ_zero`+`cassini_fibZ_step`); ★ `fibCas_det_eq_unit` — **`det 2 (fibCas n) = (−1)ⁿ⁺¹`**, the general determinant's `2×2` base *is* the orbit's conserved unit, the same unimodular `det = ±1` as the number-tower founding's shared unit `det = NS−NT = 1` (`PnFibonacciUniversal.det_pn_universal`, `det Qⁿ = unit`).  "Monic = the preserved unit" made concrete; `DetN` validated against real C-finite content.

`E213.Lib.Math.Linalg213.Permutation` — **30 PURE / 0 DIRTY**.  The permutation/sign substrate and the **Leibniz determinant**, where the **alternating** property is antisymmetrization (`theory/essays/determinant_as_quotient_characteristic.md`).  **§1**: `LPerm` (the four-constructor list permutation-equivalence `nil`/`cons`/adjacent-`swap`/`trans`), `LPerm.refl`/`LPerm.symm`, `sumZ` (Int list sum), ★ `sumZ_lperm` — **a sum is invariant under `LPerm`** (reordering preserves the sum, via Int213's propext-free `add_left_comm`); the "row swap reindexes the Leibniz sum, value unchanged" engine.  **§2**: `ltCount`/`inversions`/`psign` (`psign l = (−1)^(inversions l) = DetN.altSign (inversions l)`), ★ `psign_swap_adj` — **an adjacent swap of two distinct values flips the sign** (`psign (y::x::l) = −psign (x::y::l)` for `x≠y`), the concrete `sign(σ∘τ) = −sign σ` for an adjacent transposition (`ac_form` Nat inversion-rearrangement + `altSign_succ`, propext-free).  **§3**: `ltCount_append`, `ltCount_cons2_comm`, `psign_cons` (head factorization via `DetN.altSign_add`), ★ `psign_swap_prefix` — the sign flip for a swap of two distinct adjacent entries **after any prefix** (the bridge to swapping rows `i,i+1`).  **§4**: `prodDiagFrom`/`leibTerm`/`insertEverywhere`/`permsOf`/`perms`/`leibDet` (`leibDet n M = Σ_σ sign(σ)·Πᵢ M i (σ i)`), `leibDet_two_id` sanity (`rfl`), and the assembly lemmas `sumZ_map_neg` (pointwise negation negates the sum) + `map_lperm` (`map` is an `LPerm` congruence).    **§5**: `prodDiagFrom_append`, `rowSwapAt`/`rowSwapAt_{other,at,at1}`, `prodDiagFrom_eq_{below,above}` (rows outside `{k,k+1}` unaffected), `prodDiag_rowSwap` (diagonal products agree via `mul_left_comm`), and ★ `leibTerm_rowSwap` — an adjacent row swap (rows `k=pre.length`, `k+1`) sends the Leibniz term at `pre++y::x::l` to `−(term at pre++x::y::l)` for `x≠y`, the determinant's core combinatorial content.  (Full alternating now gates only on `perms` closed under the position-swap up to `LPerm` + nodup of `perms` elements; documented `research-notes/G185`.)

`E213.Lib.Math.Linalg213.PermClosure` — **76 PURE / 0 DIRTY**.  Toward the Leibniz determinant's **alternating** property: the enumeration `perms n` realizes the symmetric-group action.  **§0** clean ∅-axiom `List` membership (`mem_append'`/`mem_map'`/`mem_flatMap'`/`mem_singleton'` — structural on the `List.Mem` constructors, since core's `mem_*` iff-lemmas are `propext`/`Quot.sound`-tainted).  **§1** `LPerm.mem` (membership preserved), `lperm_swap_prefix`.  **§2** soundness `insEv_sound`/`permsOf_sound` (every enumerated list is a genuine rearrangement of its input).  **§3** `LPerm.length_eq`, occurrence count `cnt` + `cnt_lperm` (LPerm-invariant).  **§4** ★ `lperm_of_cnt_eq` — **count-equality ⟹ `LPerm`** (the cancellation engine: `cnt_append`/`cnt_eq_zero_nil`/`cnt_pos_mem`/`mem_split`/`lperm_mid_to_front`, with `add_left_cancel'` a propext-free replacement for the tainted `Nat.add_left_cancel`).  **§5** `swapAt_invol` + `cnt_map_inv` (count under an involution-map).  **§6** completeness `permsOf_complete` (`LPerm q xs → q ∈ permsOf xs`) — with soundness, `q ∈ permsOf xs ⟺ LPerm q xs`.  **§7** `nodup_permsOf` (the enumeration has no repeats — `removeFirst` retraction + `nodup_flatMap`/`nodup_map`/`nodup_insEv`; `Nodup L := ∀a, cnt a L ≤ 1`).  **§8** ★★★ `perms_swap_closed` — the enumeration is closed under an adjacent position-swap up to `LPerm` (via `cnt_map_inv` involution + `cnt_eq_of_iff_mem` under nodup + sound/complete); uses a clean self-defined `iota` (`List.range`'s lemmas are propext/Quot-dirty).  **§9** ★★★ `leibDet_rowSwap` — **an adjacent row swap negates the Leibniz determinant** (the per-term `leibTerm_rowSwap` over a `split_at` decomposition, `sumZ_map_neg` for the sign, `perms_swap_closed`+`map_map'`+`sumZ_lperm` for the reindex).  **§10** ★★★ `leibDet_eq_zero_of_rows_eq` — **two equal adjacent rows ⟹ `leibDet = 0`** (`leibDet_congr` pointwise + `int_eq_zero_of_eq_neg` over ℤ).  The determinant is **alternating**, ∅-axiom, via antisymmetrization — no funext/propext/Quot.  Clean ∅-axiom `List` substrate built throughout (core's `mem_*`/`length_append`/`map_map`/`range` lemmas are propext/Quot-tainted).

`E213.Lib.Math.Cauchy.CasoratianStep` — **5 PURE / 0 DIRTY**.  The discrete-Wronskian
(Abel/Liouville) law for a 3-term recurrence in subtraction-free `ℕ` form, + its telescoping:
`telescope` — `P(n+1)g(n+1)=Q(n+1)g(n) ⟹ (∏P)·g(n)=(∏Q)·g(0)` (the sign-definite ζ(3)
Casoratian `P=n³=aperyTop`, `Q=(n−1)³=aperyBot`, `g=|Cₙ|` ⟹ the cube-product telescoping
whose ratio is the `1/n³` denominator), with non-vacuous `telescope_geometric` (`rⁿ`).
`casoratian_step` — for any solutions `a,b` of `c₂·x₂=c₁·x₁+c₀·x₀`,
`c₂·(a₂·b₁)+c₀·(a₁·b₀) = c₂·(a₁·b₂)+c₀·(a₀·b₁)` (both sides `=
c₁a₁b₁+c₀a₀b₁+c₀a₁b₀`), the minus of `c₂Cₙ=−c₀Cₙ₋₁` moved across.  The middle coefficient
`c₁` cancels ⟹ the Casoratian propagates by the *outer* coefficients alone, grounding why
the Apéry-tower invariant is `deg c₂ = deg c₀` (`DepthAperyCubic`).

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

`E213.Lib.Math.Real213.FloorReferenceForm` — **2 PURE / 0 DIRTY**.  The
completability-side (disc+5, line) complement: the det-one floor's conserved golden
form `m²−mk−k²` (`ProbeTwistConic.Q_preserved`) is indefinite (`golden_indefinite`,
`Q(2,1)=+1`, `Q(1,1)=−1`) → unbounded → convergent line → the completing bottom rung
(`floor_reference_is_indefinite`).

`E213.Lib.Math.Real213.SpiralRotationInvariant` — **3 PURE / 0 DIRTY**.  The
spiral rotation invariant conserved at every turn: `Q_iterate_preserved` —
`Q(Pseq (m,k) n) = Q(m,k)` (sign-free golden form `a²+mk+k² = ab+b²+m²`) for all `n`,
by induction on the one-step `ProbeTwistConic.Q_preserved` chained through the pure
additive `add_cancel_chain` (the dirty `Nat.add_right_cancel` replaced by
`NatHelper.add_right_cancel`).  The golden form (disc `5 = NS+NT`) is the scale-invariant
of the self-similar `P`-shift.

`E213.Lib.Math.Cauchy.DepthHeightDiagonal` — **4 PURE / 0 DIRTY**.  Naming the
whole `ω^r` height-tower escapes every finite height: `heightTower c r n = expTower
c r n`, and `height_diagonal_escapes` — `diag (heightTower c) ≠ expTower c r` for
every `r` (via `DepthCeilingResidue.diag_not_in_seq`).  The residue at the height
scale, the frontier *toward* `ε₀` (no `Ordinal` constructed); `epsilon_direction`
bundles it with `coord_layer_dominates` (each layer ×`ω`).

`E213.Lens.ResidueReentry` — **2 PURE / 0 DIRTY**.  The residue re-enters as the
next operand, and the self-cover never closes: `residue_reentry_never_closes` — the
composite `P ↦ Object1 (predicateToRaw n P)` (encode the predicate to a Raw, point at
it) is not surjective (its image ⊆ `Object1`'s, which misses the residue), so re-pointing
the re-entered residue leaves a fresh residue.  `residue_perpetually_reenters` bundles:
pointing faithful-but-not-total (`object1_injective`/`object1_not_surjective`), the
residue re-encodes to a Raw (`predicateToRaw`), re-pointing never closes.  The
foundational-pointing instance of the gapless self-applying re-entry
(`Cauchy/DepthHeightDiagonal.diag_self_applies`).

`E213.Lens.Bool213.SelfReferenceForms` — **2 PURE / 0 DIRTY**.  The two
structural forms of Raw self-reference (`05_no_exterior` §5.2): `bool_not_no_fixed_point`
(the Bool `not` has no fixed point on its values `{T,F}` — the liar oscillation, period 2
never period 1) contrasted with the Nat-style Lambek period-1 self-fixed-point
(`decompose`) + well-founded descent (`depth_drops`); `self_reference_two_forms` bundles
the dichotomy.

`E213.Lib.Math.FiveFloorUnification` — **1 PURE / 0 DIRTY**.  The completability
floor and the McKay E₈ endpoint are the same atomic `P = [[2,1],[1,1]]` (disc
`5 = NS+NT`): `five_floor_unifies` bundles the det-one floor's indefinite golden form
(`FloorReferenceForm.floor_reference_is_indefinite`, the completing line bottom) with
`P mod 5` being the order-10 E₈ icosian endpoint (`MobiusPIcosian.mobius_P_meets_icosian_endpoint`).
Bottom-of-completability meets top-of-McKay at the `5`-floor (a convergence, not a
derivation; `seed/AXIOM/05_no_exterior.md` §5.6).

`E213.Lib.Math.CayleyDickson.Integer.ParabolicSignature` — **4 PURE / 0 DIRTY**.
Completes the signature dichotomy to a trichotomy: the degenerate disc-0 form
`parabForm m k = (m−k)²` is semi-definite (`parab_nonneg`, a square) with a non-origin
zero (`parab_nonorigin_zero`, `parabForm 1 1 = 0`, vanishing on a line) — the parabolic
cusp between the indefinite golden line (disc+5) and the definite Eisenstein curve
(disc−3).  `signature_trichotomy` bundles all three.

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
