# seed/ — DRLT 213 axiomatic + philosophical foundation

This directory contains the **non-Lean** foundational documents:
the axioms (English), philosophy, falsifiability claims, and
the DRLT origin narrative.  Most subsequent formalization in
`lean/E213/` is the formal counterpart of statements first
made here in prose.

## Reading order (for new arrivals)

| # | File | What it does | When to read |
|---|---|---|---|
| 1 | `ORIGIN.md` | DRLT origin story — minimal residue, 4-clause Raw axiom | First |
| 2 | `AXIOM.md` | The axiom in English: relations, distinctness, /, depth | After ORIGIN |
| 3 | `PHILOSOPHY.md` | Finitism, atomicity, why ZFC infinity fails | Before any Real213 work |
| 4 | `NOTATION.md` | Symbol conventions: NS, NT, d, c, α_GUT, K_{3,2}^{(2)} | Reference |
| 5 | `FALSIFIABILITY.md` | 14 measurement propositions that would refute DRLT | When discussing experimental tests |
| 6 | `IMPLEMENTATION.md` | Mapping seed → `lean/E213/Firmware/Raw` | When tracing axiom-to-code |
| 7 | `AUDIT_Lean.md` | Audit guide for verifying Lean ↔ seed correspondence | When auditing |
| 8 | `PAPER1.md` | Origin paper draft — superseded by `lean/E213/Math/Cohomology/Paper1Chiral.lean` | Historical |
| 9 | `CLAUDE-213.md` | Older Claude guide — superseded by root `CLAUDE.md` | Historical |

## What seed/ is NOT

- **NOT the source of truth.**  `lean/E213/` is.  When seed and
  Lean disagree, Lean wins.
- **NOT a reading order for the actual mathematics.**  For that,
  see `guide/INDEX.md` (deductively-ordered narrative).
- **NOT a paper draft.**  See `papers/README.md` (deprecated
  archive — content moved to Lean + guide).

## Cross-references

- `lean/E213/Firmware/Raw*.lean` — formal counterpart of `AXIOM.md`
- `lean/E213/Firmware/Atomicity/Five.lean` +
  `lean/E213/Firmware/Atomicity/PairForcing.lean` — formal
  counterpart of "atomicity forces (NS=3, NT=2, d=5)".
  (These were previously at `OS/` until 2026-05-XX dissolution;
  see `lean/E213/ARCHITECTURE.md` for theory.)
- `lean/E213/Physics/Foundations/FiniteUniverse.lean` — formal
  counterpart of `PHILOSOPHY.md` finitist position
- `LESSONS_LEARNED.md` (root) — guardrails extending PHILOSOPHY.md
- `lean/E213/ARCHITECTURE.md` — canonical layer architecture
  (where Firmware/Atomicity sub-cluster sits in the dependency graph)

## Status

  - `ORIGIN.md`, `AXIOM.md`, `PHILOSOPHY.md`, `NOTATION.md`: stable
  - `IMPLEMENTATION.md`, `AUDIT_Lean.md`: should track Lean refactors
  - `PAPER1.md`, `CLAUDE-213.md`: archival, not maintained
