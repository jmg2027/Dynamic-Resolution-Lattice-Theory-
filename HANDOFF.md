# Session handoff

Branch: `claude/lens-api-pointwise-rebuild-HCdLk`

The durable record of closed work lives in `lean/E213/` (source of truth) and
`theory/` (narrative).  This file keeps: this session's map, the open targets
(headline **(a)** + depth-arc A–E + scoped follow-ups), the closed-and-promoted
index, and notes/hygiene.

## Latest session (2026-06-01) — what closed

  1. **Repo consolidation / hygiene** — legacy-deletion narration stripped from
     5 theory chapters (present-state exposition); ~20 buried general-purpose
     Lean helpers hoisted into the Meta layer (NatRing/NatHelper/NatDiv213/
     Fin213/Int213), incl. the `mul_lt_mul_left_pure` Classical-guard family and
     deduped `pow_add`; seed corpus audited **already well-integrated** (no action).
  2. **Capstone rename — `G##`-prefix dropped** (CLAUDE.md rule 5).  12 modules:
     the 9 single-topic ones → `<Topic>/Capstone.lean` (matches the established
     `Capstone` convention); `G38FinalCapstone`→`HurwitzSynthesisCapstone`,
     `G39Capstone`→`NonAssocFanoCapstone`, `G6Vacuity`→`ClassAExactWitnesses`.
     Inner theorem names unchanged.  theory/math docs use topic-qualified names.
     Full build 1533 clean.
  3. **`dialogue_audit.md` chapter removed** — orphan: it claimed "Closed/PURE"
     against a `DialogueAudit/` Lean sub-tree that no longer exists (deleted in
     the 5²⁵ sweep `6b69270`; the deleted Lean was entirely the
     `maxDistinguishableCuts := 5²⁵` / `N_resolution` machinery).
  4. **propext local-purification pass — 10 theorems cleared** (swap
     propext-carrying Nat-core lemmas + Iff-closing `simp` for PURE infra):
     `KerSizeUniversal` **4 → 0** (the universal `kerSize=2` / N_gen kernel — was
     the highest-value; root = `Nat.{mul_div_cancel_left, add_mul_div_left,
     add_mul_mod_self_left, add_sub_cancel', mul_assoc}`; added
     `NatDiv213.add_mul_div_left_pure`), `EnrichedKNSNTcEvenEven` **2 → 0** +
     `PellOrbitInstances` **2 → 0** (one-line `decide_eq_true` fix, cascaded via
     import), `Choice.CanonicalTruthChar` **8 → 6**.  Now **12539 PURE / 45 real
     DIRTY / 57 sealed**; full build 1533 clean.
  5. **Classical-correspondence surface — catalog + finding** (originator
     question: "are the structural/thesis propext theorems there just to say
     'standard math's props/functions correspond like this'?" — **largely yes**).
     New `catalogs/correspondence-surface.md` classifies every DIRTY by *why* it
     carries the axiom; each category-(A) locus tagged in-source
     (`grep -rn "classical-correspondence surface" lean/`).  KEY FINDING: the
     DIRTY catalog ≈ the framework's **classical-correspondence surface**; the
     ∅-axiom core does not depend on category (A).
  6. **Seal-arc docs tempered to the empirical finding** — the earlier
     "remaining is just engineering, fix complete" claim was over-optimistic; a
     delegated migration attempt hit real walls (see **(a)**).  `STRICT_ZERO_AXIOM`,
     `theory/lens/{dirty_recovery_patterns,unified_equivalence}` corrected: the
     `universalLens` kernel hub *is* PURE-recoverable, but full `=`-form retirement
     is a foundational refactor, not bounded migration.

### The DIRTY classification (catalogs/correspondence-surface.md)

  - **(A) classical-correspondence surface** — "= the standard object" bridges;
    PURE 213-native twin (Bool lens / pointwise) carries the content, DIRTY twin
    is outward-facing, removable from the core: `BoolProp` (Bool→Prop morphism),
    `SemanticAtom.canonical*Map`, `CanonicalTruthChar`, `CupPairing.cup_symm`,
    `Hyper213Tower.lensTowerHasDistinguishing`.
  - **(B) thesis adoption** — `propAsDistinguishing*` (`propext` IS the claim that
    `Prop` occupies the distinguishing slot).  Irreducible by thesis.
  - **(C) Lens `equiv`/`refines` `=`-surface** — equivR-recoverable; the target of
    **(a)** below.
  - **(D) genuine results via classical representation** — purifiable backlog
    (`CayleyDickson.*`), same playbook as KerSizeUniversal.
  - **(E) intentional axiom exhibits / Elab plumbing / test guards** — by design.

## CLOSED this session — headline (a): foundational pointwise Lens-API rebuild

The **category-(C)** propext/Quot.sound (the universalLens refinement lattice
stated via `=`) is **retired**.  All three walls solved:

  1. **Codomain-polymorphic API** (`Lens/ReadingEquiv.lean`): `ReadingEq α`
     typeclass (per-codomain reading-sameness — `=` default, pointwise `↔` at
     `Raw → Prop`) + `Lens.equivG` / `Lens.refinesG`, reducing **definitionally**
     to `equiv` (default) and `equivR` (`Raw → Prop`).  Generic
     `equivG_slash_congruence`.  All PURE (the lone DIRTY is the intentional
     `equivR_to_equiv` bridge).
  2. **Closure companions** (wall 3, `Universal/QuotLens.lean`):
     `universalLens_{recovers_R, idempotent_R}` PURE, built on the new
     `universalLens_equivR_slash_congruence` / `combine_cong_pw` / `fold_pw`.
  3. **All consumers migrated + `=`-forms deleted**: `Lattice.{Join,
     IndexedJoin, FamilyMeet, FamilyJoin}`, `Instances.Cauchy`,
     `Algebra.Corresp`, `Choice.Resolved`, `Properties.CanonicalForm` now state
     refinement on `equivR`/`refinesG` and are **0 DIRTY**.  The DIRTY
     `universalLens_{combine_sym, view_eq, kernel_eq_E, recovers, idempotent}`
     are gone (no remaining consumers).  Full build 1533 clean; Lens-tree scan:
     the only remaining non-sealed DIRTY is `Compose.OnLens` (9, a **distinct**
     `funext`-on-`combine` mechanism → `Lens.eqPW` migration, not this API).

`propAsDistinguishing` (B) stays irreducible regardless.

## OPEN — Lens DIRTY follow-ups (distinct mechanisms, not headline (a))

  - **Equivalence-unification arc** (architecture decision — see
    **`research-notes/RFC_reading_equivalence_primitive.md`**, accepted).
    Reading-equivalence (`ReadingEq.same`) becomes 213's *canonical* equivalence
    primitive; `=` is its pure realization at concrete codomains; `propext` stays
    only at the `Prop`-atom thesis (category B).  The scattered `=`-based
    samenesses (`Lens.equiv/refines`, `HasDistinguishing.combine_sym`, kernels)
    unify into one Lens-arrow.  **P0–P3 DONE** (executed): category-C retired;
    `HasDistinguishing` stated over `same` (`autoParam` fields default `Eq` — Eq
    *instances* unedited); `universalMorphism_slash`/`_unique`/`raw_initial`
    relativized to `same`; composite instances thread `same` (`Pair`, `Sum`); the
    Lens tower (`OnLens`/`OnLensImage{,Generic,Level2}`/`TowerLevel3`) on
    `eqPW`/`sameLens` is **0 DIRTY (was 10)** — recursive via
    `universalMorphism_unique` + `sameLens`-trans/cong; dead `=`-funext lemmas
    deleted.  Remaining DIRTY = **Prop-atom thesis only** (category B:
    `propAsDistinguishing*`/`canonical*Map`/`BoolProp.universalMorphism_commute_*`),
    kept by design.  **P4 done**: `theory/lens/unified_equivalence.md` carries the
    unified narrative (reading-equivalence as the one sameness; `=` its concrete
    realization; `propext` only at the `Prop`-atom thesis).  **ARC COMPLETE
    (P0–P4).**  Full recipe + decisions: `research-notes/RFC_reading_equivalence_primitive.md`.
    **Was foundational coherence — the precision/falsifier Validation work was not
    displaced.**
    Technical investigation: `G164` (5 passes — design-C-cascade scope + the
    defeq/diamond encoding findings).
    (`GenericFamily` was the same family and is now
    PURE — pointwise-at-index.)
  - **DepthJoin** (`Instances.Leaves.DepthJoin`) — **DONE** (10 → 0): `omega` /
    `simp` / `decide`-closing-`Iff` replaced by explicit PURE Nat reasoning
    (new micro-lemmas: `two_le_add`, `eq_one_of_add_eq_two`, `max_eq_zero`,
    `two_le_of_ne_one`, `or_ge_one_of_max_ge_one`, `ge_two_of_ne_zero_ne_one`,
    `two_le_leaves_of_depth_ge_one`; tier characterized via `if_pos`/`if_neg`
    helpers).  `depth_ge_two_leaves_ge_three` also simplified (no induction).

## OPEN — smaller / scoped

  - **(d) CayleyDickson purity** (category D) — **partly done**:
    `CayleyHeavy.{normSq_eq_zero_iff, no_zero_div}` PURE (swapped `omega` /
    `Int.mul_eq_zero` → `Int213.{add_nonneg, add_eq_zero_of_nonneg,
    mul_eq_zero}`); `CDTower.CD_tower_full` PURE (cascade).  **Still DIRTY — not
    playbook swaps**: `Trig.conj_mul_anti` needs `NonAssocStarRing213 Sedenion`
    (the Sedenion→`CDDouble Cayley` bridge replicating `CayleyAlgebra213`; the
    parametric CDDouble star instance requires `[StarRing213 α]` and Cayley is
    non-associative, so it won't fire — needs a manual/weaker route) before the
    structural proof (cf. `SedenionHeavy.conj_mul_anti`) applies;
    `SedenionHeavy.flexible` is the **CDDoubleFlexible cross-pair open item**
    (`cd_flexible` needs base alternativity, which Sedenion's Cayley base lacks).
  - **Scoped doc follow-ups** (judgment/generative — do deliberately):
    G## session-tag sweep in `theory/essays` bodies; merges
    (`theory/lens/{properties,cardinality,instances,axiom_lenses}` →
    `properties_catalog`; `theory/physics/{atomic_base,atomic,capstones}`);
    splits (`cohomology/k_nm_c_classification`, `completeness_without_completeness`
    — verify first); narrative-patchwork intros (`RESEARCH_PLAN`,
    `meta/methodology_patterns`).

## OPEN — depth-arc next targets (real-number / completeness thread, A–E)

The depth arc (real = decision procedure, completeness relocated; 13 links) is
closed + promoted (`theory/math/completeness_without_completeness.md`).  The
unclaimed extensions it exposes:

  - **A. `depth_floor_is_det_one`** — DONE this prior arc (`Cauchy/DepthFloorDetOne`,
    7/0): forward (`convergent_crossdet_floor_is_one`) + converse
    (`floor_one_is_P_invariant` = `pellNormStep`).  The floor IS the P-orbit
    invariant.  Hinge between analysis-ladder and atomic forcing.
  - **B. finite-depth recurrence formal** — make "finite depth ⟺ P-recursive" a
    theorem for e (coeff `n+1`, deg 1) and π (deg 4): exhibit the explicit
    polynomial-coefficient recurrence their convergent data satisfies, prove
    `polyDepth d` matches.  Closes the classical-bridge gap.  Architecture:
    `research-notes/G155` (HolonomicReal: bundle recurrence + derived
    `CertifiedModulus`; `Holonomic.toCertifiedModulus` is the target).
  - **C. third-axis closure** — assemble `DepthDoubleExp` + `DepthExponentRecursion`
    into a positive theorem that ratio-on-exponent floors `c^{c^{poly}}` at the
    right coordinate; pin the ordinal rank `ω^r · d` for a depth-`r` tower.  The
    proven path from `ω²` toward `ω^ω`.
  - **D. Liouville's coordinate** — give `c^{k!}` (no finite `(h,d)`) a coordinate
    in the recursion hierarchy: its exponent `k!` floors under ratio (`k! ↦ k+1`);
    formalize "the exponent is itself an `expSeq`" — frontier toward `ε₀`.
  - **E. tower duality** (conceptual): GRA-tower ↔ CD-tower (level `n` loss ↔
    level `5−n` Reading-iso gain); depth-ladder ↔ Cayley–Dickson tower (both
    bottoming at the `5 = NS+NT`-forced floor); `CDDoubleFlexible` cross-pair crux
    (long-standing CD open item).  See `tower_atlas.md` / `G154` §2.

## Closed and promoted (durable homes — do not re-derive)

| Topic | Source of truth | Narrative |
|---|---|---|
| `5²⁵`-as-resolution chain — **DELETED** (originator decision); 0.2 ppb α_em result SURVIVES on π as literal input | `AlphaEM/GramStructuralCapstone` (5/0), `configCountD`/`configCount 2 = 5²⁵` bare arithmetic | `research-notes/{G156,G157}`, `RERESEARCH_n_u_removal.md` |
| Build gate-hole — CLOSED; `full_build.sh` rebuilds all 1533 modules | — | `research-notes/G159` |
| Pointwise Lens-API rebuild — category-(C) propext RETIRED; codomain-polymorphic `ReadingEq`/`equivG`/`refinesG`; universalLens refinement surface (lattice + Cauchy + Corresp + Choice + CanonicalForm) all PURE | `Lens/ReadingEquiv` (`ReadingEq`/`equivG`/`refinesG`), `Universal/QuotLens` (`kernel_eq_E_R`, `recovers_R`, `idempotent_R`, `equivR_slash_congruence`), `Theory/Raw/Fold` (`fold_slash_iff`) | `theory/lens/{dirty_recovery_patterns (P5),unified_equivalence}`, `catalogs/correspondence-surface.md`, `STRICT_ZERO_AXIOM.md` |
| Real-number completeness arc (links 1–13) | `Lib/Math/Cauchy/{Depth*,Divergence*,EulerDivergenceForm,DepthFloorDetOne}`, `Real213/*`, `Analysis/*` | `theory/math/completeness_without_completeness.md` (+ `completeness_relocated`, `probe_twist_conic`); essay `real_without_completeness.md` |
| φ self-similarity (form / count `5^L` / limit-ratio φ) | `SelfSimilarityBridge`, `Real213/{PhiAsCut,PhiConvergence,PhiNormInvariant,PhiAbCut,FibCassiniNat}`, `PellFibCutBridge` | `theory/math/phi_self_similarity.md` |
| The residue / self-covering closure | `Lens/{FlatOntologyClosure,PredicateSelfEncoding}`, `Theory/Raw/{PrimitiveTower,Lambek}` | `research-notes/G152`, `theory/essays/tower_atlas.md` |
| P-orbit closure (P self-defining; every axis sees `{3,2,1}`) | `Mobius213/Px/{CharPolySelf,MobiusSelfForm,ConvergentDet}`, `Theory/Atomicity/OrbitForcing` | `theory/essays/{every_axis_sees_p,p_orbit_closure_master}.md` |
| `Mobius213.Px` + repo-wide purity (no Classical/native_decide in 213-math) | `Mobius213/Px/*` (0 dirty) | `STRICT_ZERO_AXIOM.md` |

PURE Nat helper infrastructure (reuse, don't re-derive): `Meta/Nat/NatDiv213`
(`mul_div_self_pure`, `mul_div_cancel_left_pure`, `add_mul_div_left_pure`,
`pow_succ_div`, `add_div_right_pos`, `div_le_self_pos`), `Meta/Nat/PureNat`
(`pow_add`, `mul_assoc`, `add_mul`), `Meta/Tactic/NatHelper` (`succ_sub`,
`add_sub_cancel_right`, `add_sub_of_le`, `sub_add_cancel`, `add_mul_mod_self_pure`),
`Meta/Nat/AddMod213` (`div_le_div_right_pos`), `Lib/Math/NatRing`
(`nat_mul_assoc`, `nat_add_mul`, `mul_lt_mul_left_pure`).

## Notes / hygiene

  - **Verify Lean SEQUENTIALLY before commit**: `rm <file>.olean` → `lake env lean
    <file>` (exit 0) → `lake build <module>` → `tools/scan_axioms.py <module>`
    (N pure / 0 dirty) → commit.  build-green ≠ purity-green; never trust cached
    "Build completed"; never parallelise build with scan.
  - **propext-purification playbook** (verified — KerSizeUniversal, the Px subtree):
    Lean-core `Nat.{mul_assoc, mul_div_cancel_left, add_mul_div_left,
    add_mul_mod_self_left, add_sub_cancel', add_div_right, gcd}` all pull `propext`
    → use the `Meta/Nat` + `NatRing` PURE helpers above.  `omega` is propext-dirty
    (→ `Nat.two_mul`/`add_right_comm`/explicit).  A `simp`/`simpa` that *closes* an
    `Eq`/`Iff` goal pulls `propext` (its `of_eq_true`/`Iff→Eq` closer) → reduce with
    distribute/associate-only `simp only`, close with explicit `Iff.intro`/`rw`/
    `decide` (`decide`/`decide_eq_true`/`of_decide_eq_true` are PURE;
    `decide_eq_true_eq` is not).  `funext` = `Quot.sound` → state pointwise.
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`;
    use `Tree.noConfusion` (for `a ≠ b`).
  - **Repo-first**: grep + INDEX before coding a "missing" cell.
  - `5²⁵ = N_U = d^(d²)` as a **resolution / universe number is DELETED** — not
    deprecated, gone.  `configCountD`/`configCount 2 = 5²⁵` survive only as bare
    parametric arithmetic; never reintroduce a "the resolution" reading.  Don't
    use "ℝ = final boss" framing.
