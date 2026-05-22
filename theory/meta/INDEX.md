# theory/meta/

Meta-analysis chapters.  Mirrors **`tools/`** (not `lean/E213/Lib/`)
— these chapters narrate the meta-analysis work (Python scanners +
findings + conceptual taxonomy) produced by the
`claude/analyze-lean4-ast-patterns-49Rh2` branch (merged PR #91).

## Why `theory/meta/` exists

The strict three-tier discipline (`CLAUDE.md` "Three-tier discipline")
maps `theory/<area>/` to `lean/E213/Lib/<area>/`.  Meta-analysis is
different: the closure is in `tools/*.py` (Python scanner suite), not
in a Lean library.

Per `lean/E213/docs/PROMOTION_PATTERNS.md`: this is Pattern 1 with a
**destination variant** — the chapter mirrors `tools/` instead of
`lean/E213/Lib/`.  Promotion criteria H1-H4 are adapted: H1 (purity)
+ H2 (build clean) → H1' (scanners pass `--help`) + H2' (`lake build`
still clean, since scanners can be re-run).

## Closed chapters (2)

| Chapter | Tools / Lean sub-tree | Source notes | Promoted |
|---|---|---|---|
| [`scanner_suite.md`](scanner_suite.md) | `tools/{ast_*,syntax_*,falsifier_*}.py` (11 scanners) | G90-G103, G105, G106 (16 notes) | 2026-05-22 |
| [`raw_derivation_levels.md`](raw_derivation_levels.md) | `tools/{ast_typesig,ast_callgraph}_scan.py` + content theorems | G104 (1 note, foundational) | 2026-05-22 |

## Action-items registry — closed

The 24-item registry that the scanner suite surfaced, plus the
nine per-sub-tree deep dives that elaborated each candidate,
reached every-item closure on 2026-05-22.  See
`scanner_suite.md` §"Open frontier" for the closure summary
and `research-notes/archive/metascan/INDEX.md` for the per-note
table.

## Layout

```
theory/meta/
├── INDEX.md                     ← this file
├── scanner_suite.md             ← 11-scanner suite + key findings + cross-branch protocol
└── raw_derivation_levels.md     ← (α) logical / (β) structural / (γ) operational taxonomy
```
