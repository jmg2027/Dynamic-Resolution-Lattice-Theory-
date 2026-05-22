# research-notes/archive/audits/

Closed audit reports + draft material moved out of `research-notes/`
top-level (2026-05-21 cleanup, branch
`claude/research-notes-organization-Gr3Tp`).

Kept as **record of the path** — these were checkpoint-style audits
that informed the post-M11 hierarchical state.  Once their findings
landed in `lean/E213/ARCHITECTURE.md` and the relevant umbrella
docstrings, the audit files themselves became reference-only.

## 2026-05-05 audit triplet

| File | Scope | Status |
|---|---|---|
| `AUDIT_PASS_2026-05-05_lean.md` | `lean/E213/` tree survey | Closed; findings absorbed into ARCHITECTURE.md + `lean/E213/docs/HIERARCHICAL_PLACEMENT.md` |
| `AUDIT_PASS_2026-05-05_narrative.md` | `seed/`, `books/`, `guide/` survey | Closed; `seed/AXIOM/` is current canon; `books/`, `guide/` deleted per the audit |
| `AUDIT_PASS_2026-05-05_research-notes.md` | `research-notes/` self-survey | Closed; recommendations folded into the 2026-05-21 reorg |

## Layer character audits

| File | Scope | Status |
|---|---|---|
| `LENS_AUDIT.md` | `lean/E213/Lens/` 14→9 sub-cluster decision | Closed; cited from `Lens/API.lean` §5 + `ARCHITECTURE.md` §Lens |
| `THEORY_AUDIT.md` | `lean/E213/Theory/` Möbius promotion + Mobius213 move | Closed; cited from `Theory/Raw/API.lean` §Migration |
| `MATH_AUDIT/` (9 files) | `lean/E213/Lib/Math/` per-sub-tree audits (Foundations, Numerical, Algebra, Topology, Analysis, DyadicFSM, Cohomology, Probability, Misc) | Closed; ARCHITECTURE.md reflects the post-M11 final shape |

## Misc

| File | Theme | Status |
|---|---|---|
| `anthropic_outreach_draft.md` | Outreach draft (not sent) | Private draft, kept as record |

## Status

Don't read these for current state.  Read instead:
- `lean/E213/ARCHITECTURE.md` (current ring + sub-cluster layout)
- `lean/E213/docs/HIERARCHICAL_PLACEMENT.md` (post-M11 placement)
- `lean/E213/docs/CONSOLIDATION_PROTOCOL.md` (R1–R11 leaf rules)
- `../../INDEX.md` (current research-notes layout)
