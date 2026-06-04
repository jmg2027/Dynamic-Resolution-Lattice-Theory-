# 00 — Axioms summary

Bridge from `seed/AXIOM/` (the axiom spec) to the chapters in
`theory/`.  This is a navigation chapter, not new content.

## The axiom system (213)

213 is a 4-clause axiom over a Raw monad.  Canonical statement:
`seed/AXIOM/` (see `seed/AXIOM/INDEX.md`).

| File | What it says |
|---|---|
| `seed/AXIOM/01_residue.md` | The residue of pointing; linguistic inevitability of notation |
| `seed/AXIOM/02_axiom.md` | The 4-clause axiom; Raw structure + the forcing chain |
| `seed/AXIOM/03_form.md` | The form of the residue (source-without-enclosure); the Möbius `P` self-form (§3.5) |
| `seed/AXIOM/04_uniqueness.md` | Minimality / uniqueness of the residue |
| `seed/AXIOM/05_no_exterior.md` | No exterior; self-reference (Nat- vs Bool-style); the Möbius fixed point `P(φ)=φ` |
| `seed/AXIOM/06_lens_readings.md` | Lens readings (count-Lens, difference-Lens ℤ, `0`/`∞`, chart-local labels) |
| `seed/AXIOM/07_primacy.md` | Primacy and the one-way direction of derivation |
| `seed/AXIOM/08_falsifiability.md` | Falsifiability; the DRLT Validation Standard (precision + falsifier) |
| `seed/AXIOM/09_lean_correspondence.md` | Axiom ↔ Lean (`E213`) correspondence |
| `seed/AXIOM/10_encoding_costs.md` | Encoding costs of the formalization |

This directory holds chapters about what is **derived** from those
axioms — how the Lens fractal, the algebra tower, cohomology, gauge
emergence, etc., follow.  Each chapter cites the relevant axiom clauses
and the Lean theorems that close them.

## Companion specs (not axioms but baseline)

| File | Role |
|---|---|
| `seed/CLOSED_FORM_SPEC.md` | DRLT Closure Form conjecture: every K_{3,2}^{(c=2)} observable = R(NS,NT,d,c) · Π(1 + κ·α^n) |
| `STRICT_ZERO_AXIOM.md` | Live catalog of PURE / DIRTY theorems |
| `LESSONS_LEARNED.md` | Recurring proof-engineering patterns discovered along the path |

## How to read

1. If you've never seen 213: start with `seed/AXIOM/01_residue.md` (the residue of pointing).
2. For the formal axiom: `seed/AXIOM/02_axiom.md`.
3. For derived results: `theory/math/INDEX.md` and `theory/physics/INDEX.md`.
4. For source of truth: `lean/E213/`.
