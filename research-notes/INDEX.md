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
├── G37–G50              ← number systems + level-25 + topology (cross-cutting)
├── G59–G64              ← orthogonal-axis (companions to universe_chain)
├── G85–G87              ← cup-Δ Lens mismatch + **G86 open conjecture**
├── G88+ (2026-05-18_*)  ← lens emergence path spec
├── G107                 ← meta-scan action items (live tracker)
├── audit/               ← G17 empirical audit + G18–G27 (closed)
├── archive/             ← closed historical
│   ├── audits/          ← AUDIT_PASS_*, MATH/LENS/THEORY_AUDIT
│   ├── hodge/           ← G6–G12 (→ theory/math/cohomology/hodge_conjecture.md)
│   ├── algebra_tower/   ← G36, G51–G58 (→ theory/math/cayley_dickson/algebra_tower.md)
│   ├── universe_chain/  ← G65–G84 (→ theory/math/universe_chain.md)
│   ├── pattern_catalog/ ← G28, G30 (→ theory/math/pattern_catalog/pattern_catalog.md)
│   ├── minimal_root/    ← G31 (→ theory/math/analysis/minimal_root.md)
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

### Number systems + topology (cross-cutting, not yet promoted)

| Range | Theme |
|---|---|
| G37-G42 | Level-25 residual, 25-level algebra, octonion non-assoc, ε-δ depth modulus, 2D number grid, angle structure |
| G43-G45 | Dialogue audit, bipartite 5=3+2, cartesian vs disjoint |
| G46-G49 | Generation rule, triangular tower, operation × topology, concrete topology per floor |
| G50 | Algebra213 meta-theorems |
| G59-G64 | CDDouble lift, tower ascent fixed-point, tower candidates, ℕ→ℤ orthogonal, zero as emergent |

These are foundational cross-cutting observations spanning multiple
Lean sub-trees; no single Lean tree closes them.  Remain as active
research notes pending either consolidation or a future cross-tree
chapter.

### Cup-Δ + Cup-Leibniz (mixed: G85/G87 closed, **G86 OPEN**)

| File | Theme | Status |
|---|---|---|
| `G85_cup_delta_lens_mismatch.md` | Wedge-cup × simplicial-δ Lens incompatibility, twisted Leibniz (1,1) | Closed in `Cohomology/Cup/LeibnizUniversal.lean` |
| `G86_self_referential_lex_cup_leibniz.md` | Self-referential Leibniz of lex-projection cup, ∀(k,l) | **Open conjecture** (HANDOFF Part 2 §A; needs deep 213-native structural insight) |
| `G87_raw_native_emergence_audit.md` | Raw-native emergence audit; surfaces "6-theorem" candidate | Closed (audit document; gaps tracked for future work) |

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
| `G124_n_u_family_cross_field_connections.md` | (FROM N-U BRANCH) cross-field survey at `(d, n) = (5, 2)` — 10 directions catalogued; **OPEN frontier of the merged branch, EXCLUDED THIS SESSION** | merged-branch open survey |
| `G126_akbulut_cork_213_native.md` | Akbulut cork theorem as 213-native exotic-structure framework — supersedes FW-1.  6-phase partial close (44 PURE), signed cork-twist count = +4 | partial close — needs b_2/b_3 extension for full promotion |
| `G127_promotion_readiness_audit.md` | Per-G-marathon promotion-blocker catalog: G128/G129/G130/G126/G122 (all post-rename) | tracking / audit document |
| `G128_geometrization_open_followups.md` (was G123) | G121 post-R1 follow-ups: FW-1..FW-4 + I-series + M3/M4 — 10 marathon items dispositioned | partial close — see G127 for promotion blockers |
| `G129_v32betti_parametric_generalization.md` (was G124) | V32Betti generalization (M2 universal close); decide-based representative range done, universal Nat-quantified open | partial close — needs graph-walk infra |
| `G130_bracket_cauchy_ricci_functor.md` (was G125) | BracketCauchy ↔ IsRicciModulus typeclass framework (Option A) | OPTION A CLOSE — only S3 absorption blocks promotion |
| `G132_alphaEm_higher_cohomology_residual.md` | Sub-ppb precision via K_{3,2}^{(c=2)} higher cohomology.  **Phase 1 anchor CLOSED 2026-05-22** (`Filled3CellCohomology.lean`, 17 PURE) — shared prereq for G123 FW-2 JSJ-deepening + G126 Phase 7+ cork higher-cohomology + this campaign.  Structural finding: 3 simple 4-cycles linearly dependent (rank δ¹ = 2), giving non-trivial b_2 = 1 cohomological class at full simple-cycle filling | Phase 1 anchor done; Phases 2+ open |

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

Use next available G prefix (currently **G133**).  Once formalized:
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

11+ chapters total covering all promotable closed work
(9 Lean sub-trees + 2 meta-analysis chapters).

### Action-items archival pass (2026-05-22, branch `claude/task-organization-Vbi8u`)

After every G107 §4 item reached a final disposition (six
executed in Lean during this branch's session, four
substantively done already at audit, five structurally
infeasible per G118, one folded into G86), G107 + G108-G116
moved from top-level into `archive/metascan/`.  The closure
summary lives in `theory/meta/scanner_suite.md` §"Open
frontier".
