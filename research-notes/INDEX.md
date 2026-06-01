# research-notes/

Exploratory notes that feed the formal Lean library (`lean/E213/`)
and the narrative book (`theory/`).  Kept as **record of the path**
+ active scratchpad — not canonical statement.

## Three-tier discipline (canonical: `theory/INDEX.md`)

| Tier | Where | Purpose | Lifetime |
|---|---|---|---|
| 1. **Scratchpad** | `research-notes/` | Working memos, half-baked ideas | Volatile — once absorbed into Tier 2/3, moves to `archive/` |
| 2. **Source of truth** | `lean/E213/` | PURE-verified formal mathematics | Permanent |
| 3. **Theory book** | `theory/` | Human-readable narrative, mirrors `lean/E213/Lib/` directory shape | Permanent |

**Promotion**: when a sub-tree closes (PURE + categorically complete +
downstream-ready per `theory/PROMOTION_CRITERIA.md`), the corresponding
research notes are absorbed into a `theory/` chapter and the originals
move to `archive/`.  Three patterns documented in
`lean/E213/docs/PROMOTION_PATTERNS.md`.

Tier-1 notes here may use `G##` chronological prefix freely — they
are scratchpad-volatile, so CLAUDE.md "no session-number in
long-lived names" doesn't apply.

## Layout

```
research-notes/
├── INDEX.md             ← this file
├── 75, 76               ← semantic-atom thesis (active foundational)
├── G1–G5, G12, G29      ← foundational notes (boot-sequence + sustained reference)
├── G35                  ← 213-Algebra field catalog (17 domains, §0.5 tracks promotions)
├── G88+ (2026-05-18_*)  ← lens emergence path spec
├── audit/               ← G17 empirical audit + G18–G27 (closed)
├── archive/             ← closed historical
│   ├── audits/          ← AUDIT_PASS_*, MATH/LENS/THEORY_AUDIT
│   ├── hodge/           ← G6–G12 (→ theory/math/cohomology/hodge_conjecture.md)
│   ├── algebra_tower/   ← G36, G51–G58 (→ theory/math/cayley_dickson/algebra_tower.md)
│   ├── discrete_geometry/ ← G37–G50 (→ individual theory/math/ chapters per `discrete_geometry/INDEX.md`)
│   ├── universe_chain/  ← G65–G84 (→ theory/math/universe_chain.md)
│   ├── pattern_catalog/ ← G28, G30 (→ theory/math/pattern_catalog/pattern_catalog.md)
│   ├── minimal_root/    ← G31 (→ theory/math/analysis/minimal_root.md)
│   ├── c_counter/       ← G143, G145, G146 (→ theory/math/cohomology/k_nm_c_classification.md + 4 essays)
│   └── metascan/        ← G90–G106 (→ theory/meta/{scanner_suite,raw_derivation_levels}.md)
└── data/                ← raw evidence
    └── probes/          ← G52 algebra-tower probe txts
```

## Top-level — active reference

### Foundational (boot-sequence + sustained)

| File | Theme | Status |
|---|---|---|
| `G29_residue.md` | The residue of pointing | **Active** (boot-sequence read every session) |
| `75_semantic_atom.md` | 213 as atom of meaning + existence | Foundational thesis |
| `76_ultimate_ouroboros.md` | `Prop` instance via `propAsDistinguishing` | Companion to 75 |
| `G1_universal_lens.md` | Universal-lens unification | Anchor in `Meta/UniversalLens*` |
| `G2_trajectory_principle.md` | 4-insight unification on Raw trajectory | Cited from `LESSONS_LEARNED.md` |
| `G3_raw_as_universal_trajectory.md` | Raw = free magma on 2 generators | Anchor in `Firmware/Raw.lean` |
| `G4_chiral_phase_duality.md` | d=5 dual views (chiral / phase) | Anchor in `Math/Linalg213/PhaseChiralBridge.lean` |
| `G5_213_as_sublanguage.md` | 213 as sublanguage of mathematics | Meta-principle |
| `G12_layered_api_classification.md` | Layered API classification (Lens ring) | Cited from `Lens/API.lean` |
| `2026-05-18_lens_emergence_path.md` | Lens emergence + flat ontology spec | **12 citations** from `lean/` + `seed/` |

### Field-level catalog (mixed-status)

| File | Theme |
|---|---|
| `G35_chiral_cup_ring_catalog.md` | **213-Algebra catalog** — 17 domains, 6 conjectures C1-C6 (status tracked in §0.5; C1+C2+C3+C5+C6 promoted to `theory/`; C4 absorbed in Hodge chapter) |


### Active registries + recent G-notes (post-merge unified)

The n-u-followup branch's G107 + G108-G116 metascan cluster was
archived after every item reached final disposition (six executed
in Lean — L3/L4/L5/F/E/REAL-1 — four substantively done at audit
— L1/C/G110/G111 — five structurally infeasible per G118, one
folded into G86, one narrative-complete G117).  Closure summary
in `theory/meta/scanner_suite.md` §"Open frontier".

Active top-level registries after merge:

| File | Scope | Status |
|---|---|---|
| `G137_post_g134_merge_synthesis.md` | Cross-corpus patterns from G134 cardinality cut-off merge (3 patterns + 4 new questions) | synthesis note |
| `G138_post_merge_corpus_synthesis.md` | Whole-corpus synthesis at 103 chapters (6 patterns: modulus functor, Sym(3) spine, cut-off meta-methodology, Clause-4 recursion, Int.NonNeg bypass, multiplicity doctrine) | synthesis note |
| `archive/G139_mobius_self_form.md` | 모습 자체가 뫼비우스 행렬 — P self-form fixed point (CLOSED + PROMOTED) | promoted to `theory/math/mobius213_p_orbit_closure.md` §"Self-form fixed-point" + essay `mobius_self_form_fixed_point.md` |
| `G140_P_generates_all_nat.md` | P generates all of ℕ (PGen n ↔ n ≥ 1) — CLOSED + promoted | promoted to essay `k32_cohomology_simplex_higher_insight.md` |
| `G147_promotion_G140_G138BD.md` | Promotion note: G140 + G138 Pattern B/D higher-insight linkage | promotion record |
| `G121_dim4_self_pointing_axis.md` | dim-4 self-pointing-axis open conjecture (below Validation Standard); side-observations to `theory/math/geometrization_conjecture.md` | active scratch (chapter handles R1; note hosts open marathon front) |
| `G123_padic_next_directions.md` | Post-padic-library-closure direction note; companion to `theory/math/padic_real213.md` | active scratch (next-direction memo) |
| `G135_padic_closure_synthesis.md` | Synthesis note from post-G122 padic library closure | post-closure synthesis (could be archived) |
| `G136_kplus1_marathon_insights.md` | Insight note from G132 cup-ladder marathon; companion to `theory/math/cohomology/cup_ladder_graduation.md` | post-closure synthesis |
| `G149_analysis_continuum_space_insights.md` | Analysis / continuum / space survey — fed into G148 GRA framework + theory/math/gra_book.md Ch.6 | post-closure synthesis |
| `G155_holonomic_real_architecture.md` | HolonomicReal: modulus-as-data type architecture.  Axis 1 + the general generator → `theory/math/analysis/holonomic_modulus.md` (`Real213/{HolonomicReal,RateModulus,ExpLog/EulerModulus}`); Axes 2–3 (closure algebra, automaton reals) still open | **active** (open Axes 2–3) |
| `archive/G164_holonomic_generator_constructive_boundary.md` | The generator is total-constructive on the algebraic class AND degree-1 (e); the "LEM wall" is a rate-free artifact, not transcendence — absorbed into `theory/math/analysis/holonomic_modulus.md` §2–4 |
| `archive/G165_modulus_rate_frontier.md` | The free-total-modulus criterion `tailᵢ·k·dᵢ < 1` (rate beats the denominator-gap quantum) — absorbed into `theory/math/analysis/holonomic_modulus.md` §1, §4 |
| `RERESEARCH_n_u_removal.md` | Registry of the `5²⁵ = N_U`-as-resolution deletion (what was removed) | active registry |
| `archive/G59_generic_CDDouble_starring_lift.md` | CDDouble StarRing213 functor `[CommStarRing213 α] → StarRing213 (CDDouble α)` — absorbed into `theory/math/cayley_dickson/algebra_tower.md` "Generic-lift functor" |
| `archive/G60_tower_ascent_fixed_point.md` | Three concurrent fates (algebraic loss / Order-4 ascent / {±1} pointwise meta-fixed point) — absorbed into `theory/math/cayley_dickson/algebra_tower.md` "Three concurrent fates" |
| `archive/G61_213_tower_research_candidates.md` | 213-tower candidate enumeration — superseded by G62/G63/G64 closures |
| `archive/G62_nat_to_int_orthogonal.md` | ℕ → ℤ as orthogonal-axis quotient + property losses — absorbed into `theory/math/universe_chain.md` "Orthogonal-axis tower" |
| `archive/G63_orthogonal_axis_tower_synthesis.md` | k-axis tower `ℕᵏ → ℤᵏ⁻¹` + Eisenstein discovery at k = 3 — absorbed into `theory/math/universe_chain.md` "Orthogonal-axis tower" |
| `archive/G64_zero_as_emergent_artifact.md` | `0` as emergent quotient artifact (not derivable from Raw) — absorbed into `theory/math/universe_chain.md` "Orthogonal-axis tower" |
| `archive/G85_cup_delta_lens_mismatch.md` | Wedge-cup × simplicial-δ Lens mismatch + twisted Leibniz (1,1) — absorbed into `theory/math/cohomology/cup.md` |
| `archive/G86_self_referential_lex_cup_leibniz.md` | Self-referential Leibniz of lex-projection cup, ∀(n, k, l) — `fin_level_leibniz_general` PURE, absorbed into `theory/math/cohomology/cup.md` |
| `archive/G87_raw_native_emergence_audit.md` | Raw-native emergence audit + Clause-4 recursive atomicity → Alive derivation — absorbed into `theory/physics/foundations/atomic_constants.md` "Raw-side derivation" |
| `archive/G124_n_u_family_cross_field_connections.md` | Cross-field survey at `(d, n) = (5, 2)` — absorbed into `theory/math/cohomology/fractal.md` Open frontier "Cross-field cross-imports" |
| `archive/G125_lens_recipe_cup_catalog.md` | Lens-recipe → δ-closure catalog (`LeibnizMirror` + `LeibnizSym` + `LeibnizCatalog`) — PROMOTED to `theory/math/cohomology/cup.md` "Lens-recipe catalog" section |
| `archive/G126_akbulut_cork_213_native.md` | Akbulut cork — promoted to `theory/math/exotic_4mfd_cork.md` |
| `archive/G127_base_5_wieferich.md` | Base-5 Wieferich primes (`{20771, 40487}`) — absorbed into `theory/math/cohomology/fractal.md` Open frontier as falsifier-catalogue candidate |
| `archive/G127_promotion_readiness_audit.md` | Per-G-marathon promotion-blocker catalog — CLOSED (all five tracked marathons promoted) |
| `archive/G128_affine_plane_K25.md` | Finite-field affine-plane reading of `K_25` — absorbed into `theory/math/cohomology/fractal.md` Open frontier |
| `archive/G128_geometrization_open_followups.md` | G121 post-R1 follow-ups — substantive deepenings absorbed into `theory/math/geometrization_conjecture.md` Open Frontier |
| `archive/G129_v32betti_parametric_generalization.md` | V32Betti parametric — absorbed into `theory/math/cohomology/bipartite.md` "Parametric V32Betti" + Open Frontier |
| `archive/G130_bracket_cauchy_ricci_functor.md` | `IsModulusStructure` typeclass bridge — absorbed into `theory/math/topology.md` "Modulus structures: 3-way bridge" |
| `archive/G132_alphaEm_higher_cohomology_residual.md` | Sub-ppb precision via K_{3,2}^{(c=2)} higher cohomology — promoted to `theory/physics/alpha_em/precision_derivation.md` |
| `archive/c_counter/G143_c_multiplicity_hierarchy_refined.md` | c-multiplicity refined: (c−1)-codim falsified; enriched complex codim ≥ c — promoted to `theory/math/cohomology/k_nm_c_classification.md` + essays `c_counter_as_layer_count.md`, `disjoint_layers_as_direct_sum.md` |
| `archive/c_counter/G145_c_counter_structural_theory.md` | c-counter structural theory: multiplicity-layer interpretation + Stern-Brocot classification + K33Unified — promoted to `theory/math/cohomology/k_nm_c_classification.md` + essay `stern_brocot_as_universal_lattice.md` |
| `archive/c_counter/G146_K32_bipartite_tripartite_self_containment.md` | K_{3,2}^{(c=2)} as self-contained bipartite-tripartite — Lean Option I deferred — promoted as essay `bipartite_tripartite_self_containment.md` (Reading B) |
| `archive/G146_p_orbit_naturalness_boundary.md` | P-orbit naturalness boundary (tripartite K_{2,1,3} + ModPPeriods + POrbitClosure) — promoted to `theory/math/mobius213_p_orbit_closure.md` + essay `p_orbit_naturalness_boundary.md` |
| `archive/c_counter/G140_massey_nonvacuous_search.md` | Massey non-vacuous search at K_{3,2}^{(c=2)} (Phase 13 of G141 marathon) — closed at merge |
| `archive/c_counter/G141_cohomology_marathon.md` | 14-phase cohomology marathon — 230 PURE closed at merge; absorbed into `theory/math/cohomology/{cup_ladder_graduation,fractal,k32_higher_cohomology}.md` |
| `archive/c_counter/G142_K33_massey_full_h2_map.md` | Full H² map of K_{3,3}^{(c=2)} (all 5 dims, 4-fold Massey 5th) — absorbed into `theory/math/cohomology/k_nm_c_classification.md` |
| `archive/c_counter/G142_p_x_symmetry_classification_algorithm.md` | Algorithmic classification of P(x) symmetries — absorbed into `theory/math/mobius213_p_orbit_closure.md` Px catalog |
| `archive/c_counter/G144_p_symmetry_meta_patterns.md` | 12 meta-patterns + 4 deep insights from P(x) species programme — superseded by P-orbit closure (see `theory/math/mobius213_p_orbit_closure.md` and `theory/essays/p_orbit_closure_master.md`) |
| `archive/G154_depth_floor_is_the_p_orbit.md` | depth-floor IS the P-orbit (det 1) — closed-and-absorbed into `Cauchy/DepthFloorDetOne.lean` + `theory/math/completeness_without_completeness.md` + essays `every_axis_sees_p`/`p_orbit_closure_master` (the §2 GRA↔CD aspiration is out of scope) |
| `archive/G156_configcount_level_injectivity.md` | fractal-level tower is a strict order-embedding — result in `Cohomology/Fractal/ConfigCount.lean`; N_U-removal context in `RERESEARCH_n_u_removal.md` |
| `archive/G157_why_525_is_not_a_resolution.md` | the *why* behind the `5²⁵`-as-resolution deletion — closed decision; registry `RERESEARCH_n_u_removal.md` |
| `archive/G158_depth_floor_det_one_scoping.md` | scoping for `depth_floor_is_det_one` — target CLOSED (`Cauchy/DepthFloorDetOne.lean`, both directions) |
| `archive/G159_build_gate_hole_orphan_audit.md` | ~350-orphan build-gate hole — RESOLVED (`tools/full_build.sh` rebuilds all modules) |

Renaming note: my G123/G124/G125 collided with the n-u branch's
G123 (N_U family, promoted), G124 (cross-field survey, OPEN
frontier), G125 (Aurifeuillean, promoted).  My-side files renamed
to G128/G129/G130 to preserve the n-u promoted chapters' G-tags.

## Subdirectories

- **`audit/`** — G17 empirical pattern audit + G18-G27 classification.
  Superseded by G28/G29 conceptually; raw data retained.
- **`archive/`** — closed historical material.  Sub-clusters by topic
  (`hodge/`, `algebra_tower/`, `universe_chain/`, `pattern_catalog/`,
  `minimal_root/`, `metascan/`, `audits/`, plus pre-G era + A1-F6 series at root).
- **`data/`** — raw evidence base.  `raw_fold_slash_context.tsv`
  (G94 §C3 deliverable) + `probes/` (G52 algebra-tower 10 probe txts).

## Adding a new note

Use next available G prefix (currently **G156**).  Once formalized:
- Leave a `→ closed in <Lean module>` marker on the note
- **When a topical cluster fully closes**, promote it per
  `theory/PROMOTION_CRITERIA.md` + `lean/E213/docs/PROMOTION_PATTERNS.md`
  and move source notes to `archive/`.

## Promotion log (2026-05-21 / 2026-05-22)

Branch `claude/research-notes-organization-Gr3Tp`:

| Commit | Promotion | Pattern |
|---|---|---|
| `905c09a2` | Hodge → `theory/math/cohomology/hodge_conjecture.md` | 1 (multi-note absorption) |
| `3f9d1942` | C3 chain → `theory/physics/symmetry/c3_chain.md` | 2 (narrative-from-scratch) |
| `a3f2b585` | α_em → `theory/physics/alpha_em/precision_derivation.md` | 3 (mixed-status) |
| `b258a3f8` | C2 atomic constants → `theory/physics/foundations/atomic_constants.md` | 3 |
| `b258a3f8` | C6 cross-domain → `theory/math/cross_domain_unification.md` | 3 |
| `b258a3f8` | Algebra tower → `theory/math/cayley_dickson/algebra_tower.md` | 1 (G36, G51-G58) |
| `b258a3f8` | Pattern catalog → `theory/math/pattern_catalog/pattern_catalog.md` | 1 (G28, G30) |
| `b258a3f8` | Minimal root → `theory/math/analysis/minimal_root.md` | 1 (G31) |
| `b258a3f8` | Universe chain → `theory/math/universe_chain.md` | 1 (G65-G82) |
| `b258a3f8` | Scanner suite → `theory/meta/scanner_suite.md` | 1 + Variant A (tools-mirror; G90-G103+G105+G106) |
| `b258a3f8` | Raw-derivation levels → `theory/meta/raw_derivation_levels.md` | 1 + Variant A (G104) |

| (this session) | G131 1/α_em precision theorem (0.2 ppb) → `theory/physics/alpha_em/precision_derivation.md` (chapter expanded with C1 Step 5 closure: GramStructural/Bracket/Newton/Capstone files); G131 note archived | 3 (mixed-status: chapter expansion) |
| (this session) | G132 K_{3,2}^{(c=2)} higher cohomology sub-ppb (Phases 1-7, 89 PURE across 7 files) → `theory/physics/alpha_em/precision_derivation.md` C1 Step 6 (refined cup-ladder `‖c‖²·(α/d)^(k+1)`, sub-1·10⁻⁹ tier); G132 note archived | 3 (mixed-status: chapter expansion) |
| (this session) | G132 marathon Phases 8-19 (cup-i framework + Steenrod algebra + truncation bound, ~142 PURE across 12 files) → `theory/math/cohomology/cup_ladder_graduation.md` (new chapter) + `theory/physics/alpha_em/precision_derivation.md` C1 Step 6 expanded to 19 files / 231 PURE; insight note G136 (renumbered from G135 to avoid collision with padic_closure_synthesis G135) | 2 (narrative-from-scratch) |

| 2026-05-24 | G143 + G145 c-multiplicity + Stern-Brocot + K_{4,3} + K33Unified → `theory/math/cohomology/k_nm_c_classification.md` (new chapter, 382 lines) + 3 essays (`c_counter_as_layer_count.md`, `disjoint_layers_as_direct_sum.md`, `stern_brocot_as_universal_lattice.md`); G143/G145 archived to `research-notes/archive/c_counter/` | 2 (narrative-from-scratch) |
| 2026-05-24 | G146 P-orbit naturalness boundary + Px catalog (13 Px modules / 206 PURE) → `theory/math/mobius213_p_orbit_closure.md` (new chapter, 316 lines) + essay `p_orbit_naturalness_boundary.md`; G146_p_orbit archived | 3 (mixed-status chapter expansion + catalog synthesis) |
| 2026-05-24 | G146 K_{3,2} bipartite-tripartite self-containment (Lean Option I deferred) → essay-only `theory/essays/bipartite_tripartite_self_containment.md` (Reading B); G146_K32 archived to `research-notes/archive/c_counter/` | essay-promotion (insight without Lean) |
| 2026-05-26 | G139 모습 자체가 뫼비우스 행렬 (MobiusSelfForm.lean ~18 PURE) → `theory/math/mobius213_p_orbit_closure.md` §"Self-form fixed-point" (chapter expansion) + essay `theory/essays/mobius_self_form_fixed_point.md`; G139 archived | 3 (mixed-status: chapter expansion + essay) |
| 2026-05-28 | Marathon 16 GRA Universality (`lean/E213/Lib/Math/GRA/` umbrella, 8 files, 0 sorry — typeclass + 5 Readings + iso capstone + Phase 6 translation programme with universal depth comparison) → `theory/math/gra_book.md` + `theory/math/graded_residue_arithmetic.md` (closure status flipped from DRAFT) + essay `theory/essays/gra_universality_one_principle.md`; G148/G150/G151 archived | 3 (mixed-status: existing draft chapter + Lean-closure + essay) |

14+ chapters total covering all promotable closed work
(12 Lean sub-trees + 2 meta-analysis chapters).

### Action-items archival pass (2026-05-22, branch `claude/task-organization-Vbi8u`)

After every G107 §4 item reached a final disposition (six
executed in Lean during this branch's session, four
substantively done already at audit, five structurally
infeasible per G118, one folded into G86), G107 + G108-G116
moved from top-level into `archive/metascan/`.  The closure
summary lives in `theory/meta/scanner_suite.md` §"Open
frontier".
