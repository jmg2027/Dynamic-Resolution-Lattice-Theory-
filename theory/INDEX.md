# theory/

Human-readable narrative of the formalized DRLT-213 results.  Mirrors
the directory shape of `lean/E213/Lib/` so a reader can navigate
between code (truth) and prose (explanation) by path.

## Role in the three-tier discipline

| Tier | Where | Purpose |
|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos |
| 2. **Source of truth** | `lean/E213/` | PURE-verified Lean |
| 3. **This book** | `theory/` | Narrative + Lean references |

A chapter in `theory/` exists only when the corresponding Lean
sub-tree has **closed** per `PROMOTION_CRITERIA.md`.

## Reading order

1. `00_axioms_summary.md` — bridge from `seed/AXIOM/` (axiom spec) to
   the chapters here.  Read this first if you haven't read
   `seed/AXIOM/`.
2. `math/INDEX.md` — math chapters (closed sub-trees only).
3. `physics/INDEX.md` — physics chapters.

## Current chapters (11)

### Math (6)

| Chapter | Lean sub-tree | Promoted |
|---|---|---|
| `math/cohomology/hodge_conjecture.md` | `Lib/Math/HodgeConjecture/` | 2026-05-21 |
| `math/cayley_dickson/algebra_tower.md` | `Lib/Math/CayleyDickson/` | 2026-05-22 |
| `math/cross_domain_unification.md` | `Lib/Math/{CrossDomainUnification, ParadigmDomain*}` | 2026-05-22 |
| `math/pattern_catalog/pattern_catalog.md` | `Lib/Math/PatternCatalog/` | 2026-05-22 |
| `math/universe_chain.md` | `Lib/Math/UniverseChain/`, `Lens/Number/Nat213/`, `Lib/Math/Mobius213*` | 2026-05-22 |
| `math/analysis/minimal_root.md` | `Lib/Math/Analysis/DyadicSearch/` | 2026-05-22 |

### Physics (3)

| Chapter | Lean sub-tree | Promoted |
|---|---|---|
| `physics/symmetry/c3_chain.md` | `Lib/Physics/Symmetry/` | 2026-05-22 |
| `physics/alpha_em/precision_derivation.md` | `Lib/Physics/AlphaEM/` | 2026-05-22 |
| `physics/foundations/atomic_constants.md` | `Lib/Physics/Foundations/AtomicConstants*` | 2026-05-22 |

### Meta (2)

| Chapter | Source | Promoted |
|---|---|---|
| `meta/scanner_suite.md` | `tools/{ast_*,syntax_*,falsifier_*}.py` (11 scanners) | 2026-05-22 |
| `meta/raw_derivation_levels.md` | `tools/{ast_typesig,ast_callgraph}_scan.py` + content theorems | 2026-05-22 |

## Layout

```
theory/
├── INDEX.md                  ← this file
├── PROMOTION_CRITERIA.md     ← when a Lean sub-tree may be promoted
├── 00_axioms_summary.md      ← bridge to seed/AXIOM/
│
├── math/
│   ├── INDEX.md
│   ├── analysis/
│   │   └── minimal_root.md          (G31 — trajectory-as-witness IVT)
│   ├── cayley_dickson/
│   │   └── algebra_tower.md         (G36, G51-G58 — CD tower 4-row matrix)
│   ├── cohomology/
│   │   └── hodge_conjecture.md      (Hodge G6-G11 + 17 post-HC programme)
│   ├── pattern_catalog/
│   │   └── pattern_catalog.md       (G28, G30 — 5-entry generating set)
│   ├── cross_domain_unification.md  (G35 §C6 — graded ring across 9 domains)
│   └── universe_chain.md            (G65-G82 — atomicity → Möbius → CRT)
│
├── physics/
│   ├── INDEX.md
│   ├── alpha_em/
│   │   └── precision_derivation.md   (G35 §C1+§C5 — 0.09 ppb α_em)
│   ├── foundations/
│   │   └── atomic_constants.md       (G35 §C2 — (NS,NT)=(3,2) uniqueness)
│   └── symmetry/
│       └── c3_chain.md               (18-phase gauge emergence)
│
└── meta/                              ← mirrors tools/ (not lean/E213/Lib/)
    ├── INDEX.md
    ├── scanner_suite.md               (11-scanner meta-analysis suite, G90-G103+G105+G106)
    └── raw_derivation_levels.md       (G104 — (α)/(β)/(γ) taxonomy)
```

## How promotion works

See `PROMOTION_CRITERIA.md` for the H1-H4 + S1-S3 gates and
`lean/E213/docs/PROMOTION_PATTERNS.md` for the three operational
patterns:

1. **Multi-note absorption** (Hodge, algebra tower, pattern catalog,
   minimal root, universe chain): closed G-notes → chapter + archive.
2. **Narrative-from-scratch** (C3 chain): Lean-only work → chapter.
3. **Mixed-status absorption** (α_em, atomic constants,
   cross-domain): active multi-topic catalog where some sub-topics
   close → chapter for the closed part; catalog stays active with
   §0.5 promotion tracker.

## Active research (not promoted)

The following research-notes top-level files remain **active scratch**
(open conjectures, foundational baseline, or cross-cutting
observations not tied to a single Lean sub-tree):

- `G29_residue.md` — boot-sequence foundational read
- `G1-G5, G12` — foundational thesis (lens, trajectory, chiral, ...)
- `75, 76` — semantic atom + ouroboros
- `G35_chiral_cup_ring_catalog.md` — 213-Algebra field catalog
  (17 domains, status per-conjecture tracked in §0.5)
- `G37-G50` — number-systems + level-25 + topology cross-cutting
- `G59-G64` — orthogonal-axis tower (companions to universe chain)
- `G85-G87` — cup-Δ Lens mismatch + **G86 open conjecture
  (Cup-Leibniz general ∀(k,l))**
- `G88+` (`2026-05-18_lens_emergence_path`) — lens emergence spec
  (12 citations from `lean/` + `seed/`)
- `G107_action_items_registry.md` — meta-scan action items (live tracker; G90-G106 promoted to `theory/meta/`)
