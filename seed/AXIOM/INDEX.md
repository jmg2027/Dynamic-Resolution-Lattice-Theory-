# seed/AXIOM/ — the axiom corpus

The 4-clause Raw axiom + every document needed to *audit* the axiom
itself (falsifiability, encoding-cost analysis, self-reference,
history).

Files focused on the **Lean implementation** (faithful-emulator
analysis, device classification, audit cross-check) have been moved
to `lean/E213/AUDIT.md` (2026-05-12) — those are about the code, not
the axiom.

## Chapters

| # | File | What it covers |
|---|---|---|
| 00 | `00_nature.md` | Axiom as residue of pointing; primitive distinction; linguistic inevitability; 3-direction uniqueness (§1.1 minimum, §1.2 universal, §1.3 forced shape) |
| 01 | `01_notation_recursion.md` | The unavoidable recursion of notation (§2) |
| 02 | `02_statement.md` | The 4-clause axiom + axiom-vs-encoding-cost markers + what is **absent** (§3) |
| 03 | `03_form.md` | Why this form: austerity-as-audit; why 2 + binary; why symmetric + anti-reflexive (§4) |
| 04 | `04_falsifiability.md` | Derive-not-reconcile; §5.2.1 axiom-addition discard rule; 7 measurement falsifiers |
| 05 | `05_primacy.md` | Claim of primacy: every framework is a Lens on top (§6) |
| 06 | `06_formalization.md` | Lean correspondence notes, deprecated paper / book references (§7) |
| 07 | `07_self_reference.md` | No exterior; §8.4 dichotomy guide (re-read every Claude session) |
| 08 | `08_encoding_costs.md` | The four encoding costs of putting 213 on Lean 4 (inductive / cmp / canonical-subtype / ≠-precondition).  Why these are codomain costs, not axiom commitments. |
| 99 | `99_history.md` | Deprecated R1–R5 frame + change history of all absorbed sources |

## How to read

- **First time**: read `seed/INDEX.md` — it is self-contained with
  the axiom + key concepts in one screen.
- **For axiom understanding**: `02_statement.md` → `03_form.md` →
  `00_nature.md`.
- **For Claude session start**: `07_self_reference.md` (§8.4
  dichotomy guide) is the high-priority refresh, per CLAUDE.md boot
  sequence.
- **For falsifiability**: `04_falsifiability.md` is canonical.
- **For Lean implementation audit**: `lean/E213/AUDIT.md` +
  `08_encoding_costs.md`.

## Cross-references at seed/ root

- `seed/ORIGIN.md` — DRLT origin narrative (untouched).
- `seed/PAPER1.md` — **deleted 2026-05-12**.  Historical citations
  in Lean docstrings (`PAPER1 §X.Y`) remain as narrative references
  with no live target.
- `seed/RESOLUTION_LIMIT_SPEC.md` — N_U structural-invariant
  authority (4-domain convergence at 5²⁵).  Wins over any AXIOM/
  chapter on resolution-limit topics.
- `seed/NOTATION.md` — symbol conventions.

## Möbius interpretation — canonical location

The 4-clause axiom admits the Möbius matrix `[[2, 1], [1, 1]]` /
iterator `P(x) = (2x+1)/(x+1)` interpretation.  **Canonical
treatment**: `02_statement.md §3.4`.  Other chapters reference §3.4
rather than duplicating.

Companion: `lean/E213/Theory/Raw/Mobius.lean` (7 ∅-axiom theorems —
discriminant, trace, det, Pell-Fib recurrences) and
`research-notes/G57_213_mobius_signature.md` (multi-layer reading).

## Audit / implementation reference

The previous `08_implementation.md` (494 lines, faithful-emulator
analysis) and `09_audit.md` (374 lines, Lean × axiom cross-check)
have been moved to `lean/E213/AUDIT.md` — they audit Lean code, not
the axiom itself.  The encoding-cost framing is now `08_encoding_
costs.md` (concise restatement focusing on *why* the costs exist).
