# 213 Papers

This directory contains 16 .tex papers + the 22-chapter `drlt-book/`
monograph. They express 213 conclusions in **pre-213 mathematical
vocabulary** (Frobenius classification, π₁ topology, SU(N)
representation theory, Dieudonné determinant, Regge calculus, etc.).

## Role

These papers serve three purposes — none of them "obsolete":

1. **External communication layer.** Bridge to the existing
   mathematical and physical community using shared vocabulary. The
   audience here is researchers who do not (yet) work in 213-internal
   ontology.
2. **Idea archive.** Narrative arguments and intuitions that may guide
   future 213-internal re-derivations as marathons grow.
3. **Upper-bound progress index.** Claims here that have been closed
   at the 4/27 standard in `lean/E213/` are tracked separately
   (see `guide/STATUS.md`).

## Where to read what

For the canonical, deductively-ordered presentation of 213 results in
the cleanest currently-available vocabulary — including epistemic tags
(T0/T1/T2/T3) showing which sections are 213-internal vs. classical —
**see `guide/`** at the repository root. The guide treats `papers/`
content alongside `lean/E213/` modules and `books/` narration.

For the 213-internal narration in pure 213 vocabulary, see `books/`.

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
