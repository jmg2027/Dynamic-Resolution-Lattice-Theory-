# Session handoff

Branch: `claude/research-notes-9Nc74`

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

## OPEN — headline target (a): foundational pointwise Lens-API rebuild

Retire the **category-(C)** propext/Quot.sound (the Lens refinement lattice
stated via `=`) by redefining the Lens equivalence/refinement API pointwise.
This is the big one — **a real project, not bounded migration** (a delegated
agent attempt stalled here; broken WIP was reset).

**Three walls (empirically confirmed):**
  1. `Lens.equiv := (view x = view y)` and `refines` built on it are
     *foundational* (`Lens/LensCore.lean`) — every consumer stated through them
     inherits the `=`-cost unless the API itself is restated pointwise.
  2. `equivR`/`refinesR` are typed for `Lens (Raw → Prop)`.  The consumer lenses
     have other codomains (`iJoinLens : Lens (ι → α)`, the meets,
     `limitLens`) — P5 does not even *type* there; each needs its own
     per-codomain pointwise equivalence.  → the API must become
     codomain-polymorphic in its notion of "same".
  3. `universalLens_recovers` / `universalLens_idempotent` have **no** PURE
     `_pw` companion — they are equivalence-*closure* facts, needing closure
     lemmas re-proved on the new API.

**What already EXISTS (PURE, materialized — the hub is recoverable):**
`Lens/ReadingEquiv.lean` (`equivR`/`refinesR` + refl/symm/trans, all PURE; lone
`=`-shim `equivR_to_equiv`), `universalLens_{combine_sym,view_eq}_pw` +
`universalLens_kernel_eq_E_R` (QuotLens, PURE), `Raw.fold_slash_iff` (Theory,
PURE).  Consumers of the sealed hub `universalLens_kernel_eq_E`:
`Lattice/{Join,IndexedJoin,FamilyMeet,FamilyJoin}`, `Instances/Cauchy`,
`Algebra/Corresp`, `Choice/Resolved` (+ `Compose.OnLens*`, `Properties/CanonicalForm`,
`Cauchy/GenericFamily` carry the same `=`-shape).  `propAsDistinguishing` (B)
stays irreducible regardless.

## OPEN — smaller / scoped

  - **(d) CayleyDickson purity** (category D): `CayleyHeavy.{normSq_eq_zero_iff,
    no_zero_div}`, `SedenionHeavy.flexible`, `Trig.conj_mul_anti`,
    `CDTower.CD_tower_full` — inherited from the Lipschitz base + `Cayley.ext` +
    Int/`omega`.  Trace the root (likely the same propext-Nat/Int-core swap as
    KerSizeUniversal) and purify.
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
  - **B. finite-depth recurrence formal** — DONE FULLY (general theorem + e + π) this
    arc.  **General theorem** (`Cauchy/DepthPRecursiveInstances`, 25/0):
    `newton_polyDepth` — *every* degree-`d` discrete polynomial `Σ_{i≤d} cᵢ·binom(·,i)`
    (Newton form, 213-native `binom`, Pascal) has `polyDepth d`; exact Newton-basis
    difference (`diff_newton` lowers degree by one, iterated `d`× via `liftK_congr` +
    `liftK_diff_comm`).  `binomCol_polyDepth` = single-column case.  **e closed**:
    `e_finite_depth_iff_P_recursive` = order-1 recurrence + `polyDepth 1` ratio.
    **π closed**: `DepthPiQuartic.piRatio_polyDepth` — the full degree-4 cross-det
    ratio `4(n+1)²(2n+1)(2n+3)` has `polyDepth 4` (4 differences → const `384`),
    confirming π depth 6 ∅-axiom.  The nonlinear-Nat expansion is discharged by the
    new reflection prover **`Meta/Nat/PolyNat`** (`poly_id`, 11/0): the ∅-axiom `ring`
    replacement — reify to a polynomial tree, normalise to Horner coeffs, equal lists
    ⟹ equal by `rfl`.  Reusable Nat helpers: `add_sub_add_of_le`, `liftK_congr`,
    `binom_mono`, `poly_id`.
    **π**: `pi_is_P_recursive` (Wallis num/den order-1 recurrences, degree-2 step
    coeffs) PLUS `wallisDenCoeff_polyDepth` — the den step coefficient `(2n+1)(2n+3)`
    has a *proven* `polyDepth 2` (2nd difference = const 8; the one nonlinear-Nat
    identity `(2n+3)(2n+5) = (2n+1)(2n+3) + (8n+12)` done by hand via PURE
    `NatHelper.{add_mul,mul_assoc}`).  REMAINING sliver: the *full* degree-4 cross-det
    ratio polyDepth-4 needs the same hand-expansion 4× (degree 4→3→2→1→const), or a
    PURE nonlinear-Nat `ring`/Newton-sum kit — the real infra gap (omega is
    propext-dirty).  The G155
    HolonomicReal *type* architecture (bundle recurrence + derived `CertifiedModulus`;
    `toCertifiedModulus`) is the separate, heavier axis — needs the modulus/ValidCut
    machinery — and remains open.
  - **C. third-axis closure** — DONE this arc (`Cauchy/DepthOmegaTower`, 13/0):
    `coord_wf` — the depth-`r` tower coordinate (`r`-fold nested lex product
    `Coord r`) is well-founded for every `r`, an ordinal `< ω^r`; the whole `ω^ω`
    ladder, level by level (`coord_wf 2` recovers `DepthOrdinal`'s `ω²`).
    `coord_layer_dominates` — each exponential layer ×`ω` (one larger leading
    coeff outranks the entire lower tower).  Positive sequence companion to
    `dexp_not_const`: `dexp_exponent_floors` (the double exp's *exponent* floors
    under one ratio) + `expTower`/`expTower_succ` (value sits one `expSeq` above
    the shorter tower).
  - **D. Liouville's coordinate** — DONE this arc (`Cauchy/DepthLiouvilleCoord`,
    9/0): `liouville_exponent_coordinate` — `ratioLift fact n = (n+1)!/n! = n+1`
    (super-poly `k!` → linear in one ratio), `diff (ratioLift fact) = 1` (one diff
    floors it), `diff fact n = n·n!` (never floors on the diff axis alone).  So
    `c^{k!}`, with no finite `(h,d)`, has ratio-depth 1 / diff-depth 1 one
    recursion tier down — the concrete frontier toward `ε₀`.  PURE factorial
    (Lean-core `Nat.factorial` is Mathlib); division-cancel via `mul_div_self_pure`.
  - **E. tower duality** — OPEN CONJECTURE, not a short ∅-axiom theorem (scouted +
    scoped: `research-notes/G160`).  The GRA↔CD duality (level-`n` loss ↔ level-`5−n`
    Reading-iso gain; both bottoming at the `5 = NS+NT` floor) is `gra_book.md`
    Conjecture 5.3.1 / `tower_atlas.md` "Open frontier".  Three PURE bricks exist
    (`DepthFloorDetOne`; `GRA/DepthFunctor.depth_const`; `axis_nt_five_prime` +
    `mobius_213_discriminant`) but linking them needs (a) a formal `GRATowerLevel`
    (narrative only now), (b) the loss⟺iso-gain proof, (c) the CD flexibility crux.
    **Bundling the three `5`-facts is forbidden** (meaning-by-analogy import).  The
    one concrete sub-item is the **`CDDoubleFlexible` cross-pair** (`Meta/Algebra213`,
    all foundation PURE): `(conj d·b)·a + conj b·(d·a) = a·(conj b·d) + (a·conj d)·b`.
    Route-1 (G160): `conj_eq`-substitute both conjugates → reduces to the
    trace-commutator identity `−T_d·[a,b] − T_b·[a,d] + [a,b·d] + [a,d·b] = 0`; needs
    alternativity to close (did not close by inspection — originator's flagged crux).

## Closed and promoted (durable homes — do not re-derive)

| Topic | Source of truth | Narrative |
|---|---|---|
| `5²⁵`-as-resolution chain — **DELETED** (originator decision); 0.2 ppb α_em result SURVIVES on π as literal input | `AlphaEM/GramStructuralCapstone` (5/0), `configCountD`/`configCount 2 = 5²⁵` bare arithmetic | `research-notes/{G156,G157}`, `RERESEARCH_n_u_removal.md` |
| Build gate-hole — CLOSED; `full_build.sh` rebuilds all 1533 modules | — | `research-notes/G159` |
| Prop-codomain seal arc — single root `Lens.equiv := =`; equivR materialized PURE | `Lens/ReadingEquiv`, `Universal/QuotLens` (`*_pw`, `kernel_eq_E_R`), `Theory/Raw/Fold` (`fold_slash_iff`) | `theory/lens/{dirty_recovery_patterns (P5),unified_equivalence}`, `catalogs/correspondence-surface.md` |
| Real-number completeness arc (links 1–13 + depth-arc B/C/D) | `Lib/Math/Cauchy/{Depth*,Divergence*,EulerDivergenceForm,DepthFloorDetOne,DepthOmegaTower,DepthLiouvilleCoord,DepthPRecursiveInstances,DepthPiQuartic}`, `Meta/Nat/PolyNat`, `Real213/*`, `Analysis/*` | `theory/math/completeness_without_completeness.md` (+ `completeness_relocated`, `probe_twist_conic`); essay `real_without_completeness.md` |
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
