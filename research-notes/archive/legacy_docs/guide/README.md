# 213 Master Guide

A single living document that organizes the deductive chain of 213 / DRLT
results in the cleanest currently-available vocabulary, with explicit
epistemic tags that show how far each piece has been pulled into a
formalized 213-internal derivation.

## Why this guide exists

`papers/` is now a **DEPRECATED ARCHIVE** (see `papers/README.md`):
16 .tex papers + the 22-chapter `drlt-book/` monograph, written before
213 reached its present form and phrased in pre-213 vocabulary
(Frobenius classification, π₁ topology, SU(N) representation theory).
The current authoritative material is in `lean/E213/` + the root docs
(`HANDOFF.md`, `LESSONS_LEARNED.md`, `STRICT_ZERO_AXIOM.md`).  Cross-
references to `papers/...` below remain valid as pointers to
archived narrative content, but should not be taken as the current
state of 213.

`lean/E213/` is the formalized 213 theory body — Mathlib-free,
axiom-free for Kernel and Phase 1 Physics. But its 634 files are not
narrated as a single readable chain.

`books/` contains 213-internal narration (currently `analysis213.md`,
`periodic-table.md`); it grows one marathon at a time and is intended
to eventually replace the external-vocabulary monograph.

This guide is the **transitional bridge**. It lays out the full deductive
chain in the cleanest mixed vocabulary available now, tagged so that any
reader (or future Claude session) can see at a glance which sections are
fully internal, which are hybrid, and which still rely on external
classical math.

## Tier system

Each section is tagged with a vocabulary tier:

- **T0**  — expressible only in 213-internal vocabulary
            (Raw, swap, FluxCut, R1–R4 typeclass, Atomicity theorem)
- **T1**  — 213-internal is sharper; classical is approximation
            (cohomological derivative, dyadic MVT, (n-1)·k depth)
- **T2**  — classical adequate; 213 sharpens individual claims
            (α_em derivation chain, GUT coupling triple-path)
- **T3**  — classical only; 213 has not yet reached this domain
            (Frobenius classification, π₁ topology, BSD/Hodge/Poincaré)

As marathons close, sections migrate T3 → T2 → T1 → T0.

## How to read

- New to 213 → start at `00_meta.md`, then `INDEX.md` for navigation.
- Looking for a specific result → `INDEX.md` table.
- Tracking 4/27 standard progress → `STATUS.md`.
- Cross-reference paper claim → `appendix_paper_origins.md`.
- Cross-reference Lean module → `appendix_lean_map.md`.

## Status

- Author: Mingu Jeong (Independent Researcher).
- Acknowledgment: Drafting and synchronization performed in dialogue with
  Claude (Anthropic).
- This is a living document. Each marathon completion updates affected
  chapters and the STATUS.md tier-distribution counts.
- Not a replacement for `papers/` or `lean/E213/` — a navigational layer
  above both.
