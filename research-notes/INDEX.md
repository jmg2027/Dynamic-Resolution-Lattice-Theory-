# research-notes/

Exploratory notes that feed the formal Lean library and the
narrative book at `theory/`.  Kept as **record of the path** + active
scratchpad — not canonical statement.

## Three-tier discipline (2026-05-21)

| Tier | Where | Purpose | Lifetime |
|---|---|---|---|
| 1. **Scratchpad** | `research-notes/` | Working memos, half-baked ideas, session-bound observations | Volatile — once absorbed into Tier 2/3, moves to `archive/` |
| 2. **Source of truth** | `lean/E213/` | PURE-verified formal mathematics | Permanent |
| 3. **Theory book** | `theory/` | Human-readable narrative, mirrors `lean/E213/Lib/` directory shape | Permanent |

**Promotion rule**: when a sub-tree closes (PURE + categorically
complete + downstream-ready — see `theory/PROMOTION_CRITERIA.md`),
the corresponding research notes are absorbed into a `theory/`
chapter and the originals move to `archive/`.

Tier-1 notes here may use `G##` chronological prefix freely — they
are scratchpad-volatile, so CLAUDE.md "no session-number in
long-lived names" doesn't apply.

## Layout

```
research-notes/
├── INDEX.md             ← this file
├── 75, 76               ← semantic-atom thesis (active foundational)
├── G1–G5, G12           ← pre-audit insight notes
├── G28–G31, G35         ← post-audit + 213-algebra catalog
├── G36–G87              ← algebra tower + lens fractal + cup-Δ exploration
├── G90–G107             ← meta-scan branch deliverables (G107 = registry)
├── 2026-05-18_lens_emergence_path.md
│                        ← Lens emergence + flat-ontology spec
│                          (12 citations from lean/ + seed/, theory/
│                          promotion candidate)
├── hodge/               ← G6–G11 Hodge program closure (6 notes)
├── audit/               ← G17 empirical audit + G18–G27 iterations
├── archive/             ← closed historical drafts (pre-G + A1–F6 series)
│   └── audits/          ← closed audit reports (LENS/THEORY/MATH/AUDIT_PASS)
└── data/                ← raw evidence
    └── probes/          ← G52 algebra-tower probe txts
```

## Top-level (active reference)

### Foundational (boot-sequence + sustained reference)

| File | Theme | Status |
|---|---|---|
| `G29_residue.md` | Foundational text — the residue of pointing | **Active** (boot-sequence read every session) |
| `G28_every_pattern_present.md` | Operational primitives: every stateable pattern lives in 213 | Active (corrects G27) |
| `G30_pattern_catalog_synthesis.md` | Pattern catalog synthesis (metaformalization arc closure) | Active; cited from `Math/PatternCatalog*` |
| `75_semantic_atom.md` | 213 as the atom of meaning + existence | Foundational thesis |
| `76_ultimate_ouroboros.md` | `Prop` instance via `propAsDistinguishing` | Companion to 75 |
| `G1_universal_lens.md` | Universal-lens unification | Closed in `Meta/UniversalLens*.lean` |
| `G2_trajectory_principle.md` | 4-insight unification on Raw trajectory | Cited from `LESSONS_LEARNED.md` |
| `G3_raw_as_universal_trajectory.md` | Raw = free magma on 2 generators | Anchor in `Firmware/Raw.lean` |
| `G4_chiral_phase_duality.md` | d=5 dual views (chiral / phase) | Anchor in `Math/Linalg213/PhaseChiralBridge.lean` |
| `G5_213_as_sublanguage.md` | 213 as sublanguage of mathematics | Meta-principle |
| `G12_layered_api_classification.md` | Layered API classification (Lens ring) | Cited from `Lens/API.lean` |
| `2026-05-18_lens_emergence_path.md` | Lens emergence + flat ontology + syntactic internalization | **12 citations**; theory/ promotion candidate |

### 213-Algebra catalog + minimal-root (high-citation)

| File | Theme | Status |
|---|---|---|
| `G31_minimal_root_lens.md` | Trajectory-as-witness IVT, minimal-root cut | Skeleton closed in `Math/Analysis/DyadicSearch/MinimalRootLens.lean` |
| `G35_chiral_cup_ring_catalog.md` | **213-Algebra catalog** (880 lines, 12 domains, C1–C5 frontier) | **20 citations**; `Lib/Physics/AlphaEM/{CupChannelInventory, ProjectionRatios, ChannelCohomologyLoss, GradedDecomposition, LaplacianSpectrum, PiFiveGap}.lean` instantiate the framework |

### Algebra tower + number systems (G36–G50)

| Range | Theme |
|---|---|
| G36–G39 | Cayley-Dickson basis unification, level-25 residual, octonion non-assoc |
| G40–G42 | ε-δ modulus, 25×25 number grid, angle structure |
| G43–G45 | Dialogue audit, bipartite 5=3+2, cartesian vs disjoint |
| G46–G49 | Generation rule, triangular tower, operation × topology |
| G50 | Algebra213 meta-theorems |

### Algebra tower exploration (G51–G58)

| Range | Theme |
|---|---|
| G51–G55 | Eisenstein ladder, tower layers, type E rejection, substitution discovery, Type A residual recurrence |
| G56–G58 | Session summary, Möbius signature, tower completion |

### Lens fractal + Nat213 (G59–G75)

| Range | Theme |
|---|---|
| G59–G64 | Generic CDDouble lift, tower ascent fixed-point, tower candidates, ℕ→ℤ orthogonal, k-axis synthesis, zero as emergent |
| G65–G70 | Nat213 proper type, lenses to Nat213, Raw as fractal, finite form + atom, addition as slash-projection, atomicity (2,3,5) |
| G71–G75 | Fold direction duality, division as orthogonal-axis fold, two fold families, one as glue / 213 spiral, det = axis-generator fold |

### Closure forms (G76–G84)

| Range | Theme |
|---|---|
| G76–G79 | 213-native rotation, Lucas-Mersenne dual seven, pentagonal closure D_5, algebraic geometry / cohomology |
| G80–G82 | c=2 doubling, CRT (mod 5, mod 2), extension chain summary (G65–G81 index) |
| G83–G84 | Lens equality refactor strategy, closed-form pattern unification |

### Cup-Δ Lens mismatch + Leibniz (G85–G87)

| File | Theme | Status |
|---|---|---|
| `G85_cup_delta_lens_mismatch.md` | Wedge-cup × simplicial-δ Lens incompatibility | Closed; `Cohomology/Cup/LeibnizUniversal.lean` |
| `G86_self_referential_lex_cup_leibniz.md` | Self-referential Leibniz of lex-projection cup | **Open conjecture** (∀(k,l) general case, see HANDOFF Part 2 §A) |
| `G87_raw_native_emergence_audit.md` | 213-Raw native emergence audit (simp-4 + K_{3,2}^{(c=2)}) | Closed |

### Meta-scan branch (G90–G107)

Cross-branch deliverables from `claude/analyze-lean4-ast-patterns-49Rh2`
(merged in PR #91).  Entry point: **`G107_action_items_registry.md`**
(consolidates G90–G106 surface).

| Range | Theme |
|---|---|
| G90–G92 | AST fold motifs, syntax tactic motifs, citation graph |
| G93–G97 | 4-step handshake closure with subset-bijection branch + Lean-core dep purity audit (0 DIRTY confirmed) |
| G98–G99 | Unfold-graph implicit lemmas, rw-cascade adoption gap |
| G100–G101 | Decide-failure mining (135 falsifiers), meta-scan synthesis capstone |
| G102–G106 | Full Expr callgraph, Raw-depth + Expr-shape, derivation three levels, recursor inventory, L1 Expr extraction |
| **G107** | **Action items registry** (24 surfaced items + ranked execution order + theory-doc candidates) |

## Subdirectories

- **`hodge/`** — G6–G11 Hodge program closure (6 notes).  Reading
  order + Lean closure mapping in `hodge/INDEX.md`.  All closed in
  `Math/Cohomology/HodgeConjecture/`.  **Hodge promotion candidate
  for first theory/ batch.**

- **`audit/`** — G17 empirical pattern audit (6125 decls) + G18–G27
  classification iterations.  Superseded by G28/G29 conceptually;
  raw audit data retained as evidence base.  See `audit/INDEX.md`.

- **`archive/`** — closed historical exploratory drafts.  Pre-G era
  (17/19/30), kernel cardinality (A1/B1/B2/C1), resolution-limit
  early framing (D1/D2/D3), Real213 analysis (E1–E5), Real213
  marathon final state (F0–F6).  Subdirectory:
  - **`archive/audits/`** — closed audit reports
    (`LENS_AUDIT.md`, `THEORY_AUDIT.md`, `MATH_AUDIT/`,
    `AUDIT_PASS_2026-05-05_*`) + private draft (`anthropic_outreach_draft.md`).

- **`data/`** — raw evidence base.
  - `raw_fold_slash_context.tsv` — fold/slash context atlas (G94 §C3 deliverable)
  - **`probes/`** — G52 algebra-tower probe txts (10 files, 2026-05-09 marathon)

## Adding a new note

Use next available G prefix (currently G108).  Once formalized:
- Leave a `→ closed in <Lean module>` marker on the note
- **When a topical cluster fully closes**, promote it as a chapter
  in `theory/` per `theory/PROMOTION_CRITERIA.md` and move the
  source notes to `archive/`.

## 2026-05-21 reorg (branch `claude/research-notes-organization-Gr3Tp`)

- **C1**: 18 misplaced files moved out:
  - `CONSOLIDATION_PROTOCOL.md`, `HIERARCHICAL_PLACEMENT.md` →
    `lean/E213/docs/` (Lean-tree maintenance docs)
  - `AUDIT_PASS_2026-05-05_*` (3), `LENS_AUDIT.md`,
    `THEORY_AUDIT.md`, `MATH_AUDIT/` (10), `anthropic_outreach_draft.md`
    → `archive/audits/` (closed audit reports)
  - `G52_probe_*.txt` (10) → `data/probes/` (raw evidence)
- **C2**: `theory/` skeleton created with `PROMOTION_CRITERIA.md`
- **C3**: First promotion — Hodge program closure to
  `theory/math/cohomology/hodge_conjecture.md`
