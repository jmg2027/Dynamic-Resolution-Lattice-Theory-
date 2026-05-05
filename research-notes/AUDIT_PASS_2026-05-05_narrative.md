# AUDIT_PASS 2026-05-05 — books/, guide/, seed/

Survey of the narrative tier (NARRATIVE + META layers per CLAUDE.md
repository layout).

## File counts

| Dir | Files | Purpose |
|---|---|---|
| `seed/` | 10 | Foundational documents (META) |
| `guide/` | 21 | Master deductive guide (16 chapters + appendices) |
| `books/` | 11 | 213-internal narrative (math/ + physics/) |

## seed/ status

  - `ORIGIN.md`, `AXIOM.md`, `PHILOSOPHY.md`, `NOTATION.md` —
    foundational, stable.
  - `RESOLUTION_LIMIT_SPEC.md` — canonical mechanical-spec for
    cardinality / N_U / type-preservation.
  - `FALSIFIABILITY.md`, `IMPLEMENTATION.md`, `AUDIT_Lean.md` —
    operational specs, stable.
  - `PAPER1.md` — original seed paper (kept for historical reference).
  - `INDEX.md` — UPDATED in this audit pass to add
    `RESOLUTION_LIMIT_SPEC.md` row + correct PHILOSOPHY.md description.

## guide/ status

21 files: 16 chapters (00_meta through 15_metalogic) + STATUS.md +
INDEX.md + appendix_paper_origins.md + appendix_lean_map.md +
README.md.  Wording sweep grep returned **no hits** for the
deprecated framing in `guide/`.  No action needed.

## books/ status

11 files split into `math/` (cohomology-213, number-theory-213,
linalg-213, universal-lens-213, probability-213, analysis213,
INDEX.md) and `physics/` (diamond.md and others).  Wording sweep
grep returned **no hits**.  No action needed.

## Recommendations

  - No moves, merges, or wording changes recommended for `seed/`,
    `guide/`, or `books/` beyond what was already executed in this
    audit pass.
  - The narrative tier is well-organised and consistent with the
    new RESOLUTION_LIMIT_SPEC framing.

## Cross-references updated in this audit pass

  - `seed/INDEX.md` — add `RESOLUTION_LIMIT_SPEC.md` row, correct
    PHILOSOPHY.md description (no longer "why ZFC infinity fails").
  - `papers/README.md` (top-level) — replaced "finitist-by-theorem"
    framing with structural-invariant pointer.
