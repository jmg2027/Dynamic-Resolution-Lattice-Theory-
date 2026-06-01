# Session handoff

Branch: `claude/lens-api-pointwise-rebuild-HCdLk`

Durable closed work lives in `lean/E213/` (source of truth) and `theory/`
(narrative); `catalogs/`, `STRICT_ZERO_AXIOM.md`, and `research-notes/` carry
status + scratch.  This file keeps the current open targets, the closed index,
and hygiene notes.

## State

The **Lens tree is 0 real DIRTY** (sealed-by-design = the `Prop`-atom thesis
only: `propAsDistinguishing*` / `canonical*Map` / `BoolProp.universalMorphism_commute_*`,
where `propext` *is* the content).  213's equivalence is unified on
reading-equivalence: `ReadingEq.same` is the canonical sameness, Lean `=` its
realization at concrete codomains, pointwise `↔`/`sameLens` where `=` would
import `funext`/`propext`.  Full build (1533 modules) clean.

## OPEN — targets

### Validation core — the DRLT Standard (the real target)

`CLAUDE.md` "DRLT Validation Standard": from `(NS, NT, d) = (3, 2, 5)` atomicity,
0 free parameters, satisfy at least one strict ∅-axiom result —
  - **precision theorem** at ppb–ppm: `1/α_em`, `m_μ/m_e` (`NS·137/NT`, 0.48 ppb),
    `m_p` (`NS·Λ_QCD·P`), `R∞` (4.3 ppb), `Ω_Λ` (0.0008 %);
  - **falsifier** (measurable): `N_gen = C(NS,NT) = 3`, `θ_QCD ∈ [2.5,3.0]×10⁻¹¹`,
    neutrino normal ordering, Cabibbo `λ = 5/22`.

Catalogs: `catalogs/{physics-constants,falsifiers}.md`.  **Real target**: precision
theorem AND falsifier for the same observable.  Next concrete step: audit which
of these are *strict ∅-axiom* in Lean vs which are still Python/numerical or
carry gaps (e.g. `AlphaEM/GramStructuralCapstone` for `1/α_em`).  Foundational
hygiene must not displace this.

### CayleyDickson remaining (category D)

  - `Trig.conj_mul_anti` — **CLOSED (∅-axiom)**.  Added `NonAssocStarRing213
    Sedenion` (`SedenionAlgebra213`, the manual componentwise route — Cayley
    is non-associative so the parametric `[StarRing213 α]` CDDouble star instance
    cannot fire); `TrigintaduoionionHeavy.conj_mul_anti` is now the verbatim
    structural analog of `SedenionHeavy.conj_mul_anti` one layer up.
  - `SedenionHeavy.flexible` — **crux closed; concrete closure pending.**  The
    long-standing `CDDoubleFlexible` cross-pair `(conj d·b)·a + conj b·(d·a) =
    a·(conj b·d) + (a·conj d)·b` is now proved ∅-axiom (`FlexAlt213.flex_cross_pair`,
    via `left_alt_polar`/`right_alt_polar` → alternating associator + central
    trace).  Still needed to land `SedenionHeavy.flexible` itself: (i) register
    `FlexAlt213 Cayley` (needs generic CDDouble nuclearity `ofInt_nuc_{l,m,r}` +
    `TraceNormed213 (CDDouble α)` + `conj_mul_self`, none present yet), then
    (ii) the concrete `re`/`im` assembly on `Sedenion` from `flex_cross_pair` +
    `conj_sandwich` + base `flexible` (the `re`-split is `L1=R1`/`L4=R3`/cross-pair;
    the `im`-component identity is not yet derived) — or, alternatively,
    generalize `Mul (CDDouble α)` / `CDDouble.conj` to a `[NonAssocStarRing213 α]`
    base so the abstract `cd_flexible` can be stated and the Sedenion→`CDDouble
    Cayley` bridge reused.

### Depth-arc (real-number / completeness thread, B–E)

Depth arc closed + promoted (`theory/math/completeness_without_completeness.md`);
unclaimed extensions:
  - **B. finite-depth recurrence** — make "finite depth ⟺ P-recursive" a theorem
    for e (coeff `n+1`, deg 1) and π (deg 4): exhibit the polynomial-coefficient
    recurrence their convergents satisfy, prove `polyDepth d` matches.
    Architecture: `research-notes/G155` (`Holonomic.toCertifiedModulus`).
  - **C. third-axis closure** — assemble `DepthDoubleExp` + `DepthExponentRecursion`
    into a positive theorem that ratio-on-exponent floors `c^{c^{poly}}`; pin the
    ordinal rank `ω^r · d` for a depth-`r` tower (path from `ω²` toward `ω^ω`).
  - **D. Liouville's coordinate** — give `c^{k!}` a coordinate (its exponent `k!`
    floors under ratio, `k! ↦ k+1`); formalize "the exponent is itself an `expSeq`"
    (frontier toward `ε₀`).
  - **E. tower duality** (conceptual) — GRA-tower ↔ CD-tower; depth-ladder ↔
    Cayley–Dickson tower (both bottoming at the `5 = NS+NT` floor).  See
    `theory/essays/tower_atlas.md`.

### Scoped doc follow-ups (judgment / generative)

Merges (`theory/lens/{properties,cardinality,instances,axiom_lenses}` →
`properties_catalog`; `theory/physics/{atomic_base,atomic,capstones}`); splits
(`cohomology/k_nm_c_classification`, `completeness_without_completeness` — verify
first); narrative-patchwork intros (`RESEARCH_PLAN`, `meta/methodology_patterns`).

## Closed (durable homes — do not re-derive)

| Topic | Source of truth | Narrative |
|---|---|---|
| Equivalence unification — 213's sameness is reading-equivalence (`ReadingEq.same`); `HasDistinguishing` stated over `same`; composite instances thread `same` (`Pair`/`Sum`); Lens tree 0 real DIRTY | `Lens/ReadingEquiv` (`ReadingEq`/`equivG`/`refinesG`), `Lens/EqPW` (`sameLens` + laws), `Lens/SemanticAtom` (`combine_sym`/universal morphism over `same`), `Universal/QuotLens` (`kernel_eq_E_R`, `recovers_R`, `idempotent_R`), `Theory/Raw/Fold` (`fold_slash_rel`, `fold_slash_iff`) | `theory/lens/{unified_equivalence,dirty_recovery_patterns}`, `research-notes/RFC_reading_equivalence_primitive.md` (+ `G164`), `STRICT_ZERO_AXIOM.md`, `catalogs/correspondence-surface.md` |
| `omega`/`simp` purifications — `Instances.Leaves.DepthJoin` (tier classification), `CayleyDickson.{CayleyHeavy,CDTower}`, `Cauchy.GenericFamily` (pointwise-at-index) all PURE | the modules above; general Nat/`max` helpers in `Meta/Tactic/NatHelper`, Int helpers in `Meta/Int213` | `STRICT_ZERO_AXIOM.md`, `catalogs/correspondence-surface.md` |
| `5²⁵`-as-resolution chain — DELETED (originator); 0.2 ppb α_em result survives on π as literal input | `AlphaEM/GramStructuralCapstone` (5/0), `configCountD`/`configCount 2 = 5²⁵` bare arithmetic | `research-notes/{G156,G157}`, `RERESEARCH_n_u_removal.md` |
| Real-number completeness arc (links 1–13) | `Lib/Math/Cauchy/{Depth*,Divergence*,EulerDivergenceForm,DepthFloorDetOne}`, `Real213/*`, `Analysis/*` | `theory/math/completeness_without_completeness.md` (+ `completeness_relocated`, `probe_twist_conic`); essay `real_without_completeness.md` |
| φ self-similarity (form / count `5^L` / limit-ratio φ) | `SelfSimilarityBridge`, `Real213/{PhiAsCut,PhiConvergence,PhiNormInvariant,PhiAbCut,FibCassiniNat}`, `PellFibCutBridge` | `theory/math/phi_self_similarity.md` |
| The residue / self-covering closure | `Lens/{FlatOntologyClosure,PredicateSelfEncoding}`, `Theory/Raw/{PrimitiveTower,Lambek}` | `research-notes/G152`, `theory/essays/tower_atlas.md` |
| P-orbit closure (P self-defining; every axis sees `{3,2,1}`) | `Mobius213/Px/{CharPolySelf,MobiusSelfForm,ConvergentDet}`, `Theory/Atomicity/OrbitForcing` | `theory/essays/{every_axis_sees_p,p_orbit_closure_master}.md` |
| Repo-wide purity (no Classical/native_decide in 213-math) | `Mobius213/Px/*` (0 dirty) | `STRICT_ZERO_AXIOM.md` |

PURE Nat/Int helper infrastructure (reuse, don't re-derive): `Meta/Nat/NatDiv213`
(`mul_div_self_pure`, `mul_div_cancel_left_pure`, `add_mul_div_left_pure`,
`pow_succ_div`, `add_div_right_pos`, `div_le_self_pos`), `Meta/Nat/PureNat`
(`pow_add`, `mul_assoc`, `add_mul`), `Meta/Tactic/NatHelper` (`succ_sub`,
`add_sub_cancel_right`, `sub_add_cancel`, `add_mul_mod_self_pure`, `le_max_left/right`,
`max_comm`, `two_le_add`, `eq_one_of_add_eq_two`, `max_eq_zero`, `two_le_of_ne_one`,
`ge_two_of_ne_zero_ne_one`, `or_ge_one_of_max_ge_one`), `Meta/Nat/AddMod213`
(`div_le_div_right_pos`, `add_mod_gen`), `Meta/Int213` (`add_nonneg`,
`add_eq_zero_of_nonneg`, `mul_eq_zero`), `Lib/Math/NatRing`
(`nat_mul_assoc`, `nat_add_mul`, `mul_lt_mul_left_pure`).

## Notes / hygiene

  - **Verify Lean SEQUENTIALLY before commit**: `rm <file>.olean` → `lake env lean
    <file>` (exit 0) → `lake build <module>` → `tools/scan_axioms.py <module>`
    (N pure / 0 dirty) → commit.  build-green ≠ purity-green; never trust cached
    "Build completed"; never parallelise build with scan.  **`lake build` (default
    target) does NOT cover every module** (e.g. `Compose.OnLens`) — verify changed
    modules explicitly or with the comprehensive build.
  - **propext-purification playbook** (verified): Lean-core `Nat.{mul_assoc,
    mul_div_cancel_left, add_mul_div_left, add_mul_mod_self_left, add_sub_cancel',
    add_div_right, gcd}` pull `propext` → use the `Meta/Nat` + `NatRing` helpers.
    `omega` is propext-dirty (→ explicit `Nat`/`NatHelper`).  A `simp`/`simpa` that
    *closes* an `Eq`/`Iff` goal pulls `propext` → reduce with `simp only`
    distribute/associate, close with explicit `Iff.intro`/`rw`/`decide`
    (`decide`/`decide_eq_true`/`of_decide_eq_true` PURE; `decide_eq_true_eq` not).
    `funext` = `Quot.sound` → state pointwise (`fold_slash_rel`/`eqPW`/`sameLens`).
  - **Reading-equivalence is the sameness primitive**: when a `=` of views /
    functions / Lenses would pull `funext`/`propext`, state it up to `same`
    (`equivR`/`sameLens`/the codomain's `ReadingEq.same`).  `=` stays only where it
    is axiom-free (concrete codomains) or where it *is* the thesis (`Prop`-atom).
    See `research-notes/RFC_reading_equivalence_primitive.md`.
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`;
    use `Tree.noConfusion` (for `a ≠ b`).
  - **Repo-first**: grep + INDEX before coding a "missing" cell.
  - `5²⁵ = N_U = d^(d²)` as a **resolution / universe number is DELETED** — gone,
    not deprecated.  `configCountD`/`configCount 2 = 5²⁵` survive only as bare
    parametric arithmetic; never reintroduce a "the resolution" reading.  Don't use
    "ℝ = final boss" framing.
