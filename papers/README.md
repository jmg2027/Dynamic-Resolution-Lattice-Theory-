# 213 Papers — DEPRECATED ARCHIVE (do not consult as authoritative)

> ⚠️ **Status (2026-05-01): Deprecated archive.**  Do NOT use these
> files as the current state of 213.  They predate the finitist
> closure (`ValidationStandardOne.lean`, `PureAtomicObservables.lean`,
> `AlphaEMMasterCapstone.lean`) and the L1-strong rational-complex
> principle.
>
> **Current authoritative material** — Lean theorems in `lean/E213/`
> + `HANDOFF.md` (root) + `LESSONS_LEARNED.md` + the closure-algorithm
> doc in `rust-engine/docs/`.  Use those, not this directory.

## What this directory was

16 .tex papers + the 22-chapter `drlt-book/` monograph, expressing
213 conclusions in **pre-213 mathematical vocabulary** (Frobenius
classification, π₁ topology, SU(N) representation theory, Dieudonné
determinant, Regge calculus, etc.).  Originally intended as external
communication layer for non-213-native readers.

## Why deprecated

  1. **Vocabulary mismatch with current 213**: papers use ZFC-style
     "asymptote", "limit", "transcendental input" framing.  213 is
     now formalized as finitist-by-theorem (see CLAUDE.md "Finitism
     is Forced, Not Chosen") — the paper framing is structurally
     incompatible with the proven cut-algebra obstruction.
  2. **Stale claims**: numerical agreements quoted in papers were
     superseded by sub-ppb closures (α_em 0.18 ppb, m_p/m_e
     0.06 ppm, m_n/m_p 1 ppb, etc.) — the papers' precision tables
     are old.
  3. **No 0-axiom cite path**: papers reference Lean modules that
     have since been refactored or absorbed; cite chain broken.

## What replaced this

| Was in `papers/` | Now lives in |
|---|---|
| 213 closed-form derivations | `lean/E213/Physics/*.lean` (0-axiom) |
| Narrative + theorem map | `guide/INDEX.md` + chapters |
| Master atomic catalog | `catalogs/atomic-integers.md` + `rust-engine/docs/closure-algorithm.md` |
| External-vocabulary translation | (no current authoritative version — to be re-built when needed) |

## If you want to read the old papers anyway

They are kept as historical record.  Treat any specific claim as
"archived hypothesis" — verify against current Lean theorems before
citing.  See `guide/STATUS.md` for which papers' content is closed
at the current 0-axiom standard.

## Structure

- `paper{1..16}*.tex` — individual journal-style papers. See
  `guide/appendix_paper_origins.md` for the reverse map of which
  paper corresponds to which guide chapter.
- `drlt-book/` — 22-chapter monograph. Comprehensive but written in
  pre-213 vocabulary. Chapter ↔ guide map in
  `guide/appendix_paper_origins.md`.
- `paper15_ns_gram_ERRATUM.md`, `paper15_ns_gram_v2_abstract.md`,
  `paper16_v2_plan.md`, `prime_numbers_from_finite_geometry.md` —
  supplementary notes and revision drafts.

## Status

Papers and Lean are **complementary by design**, not competitors:

- Papers prove "the conclusions match what existing physics says".
- Lean proves "the conclusions follow from the 4-clause raw axiom".

Both kinds of proof are needed. Neither replaces the other.

## Author

- Mingu Jeong (Independent Researcher).
- Acknowledgment in each paper: "This work was developed in dialogue
  with Claude (Anthropic)."

## License

Prose under CC BY-NC-ND 4.0 (see repository root `LICENSE-DOCS`).
