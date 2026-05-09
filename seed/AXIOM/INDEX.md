# seed/AXIOM/ — the axiom corpus

The 4-clause Raw axiom + every document needed to audit it
(falsifiability, Lean implementation analysis, audit checklist).

This directory **replaces** the former 5 flat files —
`AXIOM.md`, `PHILOSOPHY.md`, `FALSIFIABILITY.md`,
`IMPLEMENTATION.md`, `AUDIT_Lean.md` — with a chapter-organized
sub-directory.  Content is preserved verbatim; only the
container shape changed.

## Chapters

| # | File | What it covers |
|---|---|---|
| 00 | `00_nature.md` | Axiom as residue of pointing; primitive distinction; linguistic inevitability; 3-direction uniqueness (§1.1 minimum, §1.2 universal, §1.3 forced shape) |
| 01 | `01_notation_recursion.md` | The unavoidable recursion of notation (§2) |
| 02 | `02_statement.md` | The 4-clause axiom + what is **absent** from it (§3) |
| 03 | `03_form.md` | Why this form: austerity-as-audit; why 2 + binary; why symmetric + anti-reflexive (§4) |
| 04 | `04_falsifiability.md` | Derive-not-reconcile; §5.2.1 axiom-addition discard rule; 7 measurement falsifiers |
| 05 | `05_primacy.md` | Claim of primacy: every framework is a Lens on top (§6) |
| 06 | `06_formalization.md` | Lean correspondence, encoding artifacts, deprecated paper / book references (§7) |
| 07 | `07_self_reference.md` | No exterior; §8.4 dichotomy guide (re-read every Claude session) |
| 08 | `08_implementation.md` | Raw + Theory faithful-emulator analysis (α/β/γ/δ classification) |
| 09 | `09_audit.md` | Lean ↔ axiom cross-check + corner cases + 5 leak paths |
| 99 | `99_history.md` | Deprecated R1–R5 frame + change history of all absorbed sources |

## How to read

- **First time**: read `seed/INDEX.md` — it is self-contained
  with the axiom + key concepts in one screen.
- **For audit**: `02_statement.md` → `09_audit.md` →
  `08_implementation.md`.
- **For Claude session start**: `07_self_reference.md` (§8.4
  dichotomy guide) is the high-priority refresh, per CLAUDE.md
  boot sequence.
- **For falsifiability**: `04_falsifiability.md` is canonical.

## Cross-references at seed/ root

- `seed/ORIGIN.md` — DRLT origin narrative (untouched).
- `seed/PAPER1.md` — archival paper (cited by ~25 Lean files
  via `PAPER1 §X.Y`; do not modify).
- `seed/RESOLUTION_LIMIT_SPEC.md` — N_U structural-invariant
  authority statement (4-domain convergence at 5²⁵; cardinality
  as lens output; Cantor + Cauchy under ∅-axiom).  The
  `RESOLUTION_LIMIT_SPEC.md` wins when it diverges from any
  AXIOM/ chapter on the resolution-limit topic.
- `seed/NOTATION.md` — symbol conventions.

## Möbius signature appendices (2026-05-09)

The 4-clause axiom admits an algebraic encoding as the Möbius
matrix `[[2, 1], [1, 1]]` corresponding to the iterator
`P(x) = (2x+1)/(x+1)`.  Cross-references:

- `02_statement.md §3.4` — algebraic signature interpretation
  (trace 3 = NS, det 1, disc 5 = NS+NT, eigenvalues φ², 1/φ²)
- `03_form.md §4.4` — `(x+1) → (2x+1)` iterator as Raw's natural
  form induced by minimum "two + binary" axiom
- `07_self_reference.md §8.5` — Möbius P(x) as concrete model
  of the self-reference loop; fixed point φ = minimum residue

These additions are *interpretive*, not modifications to the
axiom.  The bridge theorem is at `lean/E213/Theory/Raw/Mobius.lean`
(7 ∅-axiom theorems including discriminant, trace, det, Pell-Fib
recurrences).

The same φ appears in DRLT physics (CKM δ = π/φ², Cabibbo
Wolfenstein A = φ/c, neutrino mass ratios) and in the algebra
tower asymptote (1 − 0.5/φ^rank).  See `research-notes/G57_213
_mobius_signature.md` for the full multi-layer reading.
