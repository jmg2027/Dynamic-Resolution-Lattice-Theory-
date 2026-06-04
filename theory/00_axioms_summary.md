# 00 — Axioms summary

Bridge from `seed/AXIOM/` (the axiom spec) to the chapters in
`theory/`.  This is a navigation chapter, not new content.

## The axiom system (213)

213 is a 4-clause axiom over a Raw monad.  Canonical statement:
`seed/AXIOM/`.

| Chapter | File | What it says |
|---|---|---|
| 00 | `seed/AXIOM/01_residue.md` | Nature of the axiom: pointing, linguistic inevitability |
| 01 | `seed/AXIOM/01_nat.md` | The 4-clause axiom |
| 02 | `seed/AXIOM/02_structure.md` | Raw structure + Lens |
| 03 | `seed/AXIOM/03_resolution.md` | Resolution limit (N_U = 5²⁵) |
| 04 | `seed/AXIOM/08_falsifiability.md` | DRLT Validation Standard (precision + falsifier) |
| 05 | `seed/AXIOM/05_formalization.md` | Formalization conventions |
| 06 | `seed/AXIOM/09_lean_correspondence.md` | (continued) |
| 07 | `seed/AXIOM/05_no_exterior.md` | Self-reference + absence of exterior |
| 09 | `seed/AXIOM/06_lens_readings.md` | Chart-local labels (§9.1), syntactic internalization (§9.4) |

Once `seed/AXIOM/` chapters are settled, this directory holds
chapters about what is **derived** from those axioms — how the
Lens fractal, the algebra tower, cohomology, gauge emergence, etc.,
follow.  Each chapter cites the relevant axiom clauses and the
Lean theorems that close them.

## Companion specs (not axioms but baseline)

| File | Role |
|---|---|
| `seed/RESOLUTION_LIMIT_SPEC.md` | N_U = 5²⁵ as count-Lens readout at fractal level 2; replaces "finitism" framing |
| `seed/CLOSED_FORM_SPEC.md` | DRLT Closure Form conjecture: every K_{3,2}^{(c=2)} observable = R(NS,NT,d,c) · Π(1 + κ·α^n) |
| `STRICT_ZERO_AXIOM.md` | Live catalog of PURE / DIRTY theorems |
| `LESSONS_LEARNED.md` | Recurring patterns (#1–#13) discovered along the path |

## How to read

1. If you've never seen 213: start with `seed/AXIOM/01_residue.md` (the residue of pointing).
2. For the formal axiom: `seed/AXIOM/01_nat.md`.
3. For derived results: `theory/math/INDEX.md` and
   `theory/physics/INDEX.md`.
4. For source of truth: `lean/E213/`.
