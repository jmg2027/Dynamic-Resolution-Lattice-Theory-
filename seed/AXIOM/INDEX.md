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
| 08 | `08_implementation.md` | Raw + Firmware faithful-emulator analysis (α/β/γ/δ classification) |
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
- `seed/NOTATION.md` — symbol conventions.
