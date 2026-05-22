# seed/AXIOM/ — the axiom corpus

The 4-clause Raw axiom + every document needed to *audit* the axiom
itself (falsifiability, encoding-cost analysis, self-reference,
history).

Lean implementation audit (faithful-emulator analysis, device
classification, axiom cross-check) lives at `lean/E213/AUDIT.md`.

## Chapters

| # | File | What it covers |
|---|---|---|
| 00 | `00_nature.md` | Axiom as residue of pointing; primitive distinction; linguistic inevitability; 3-direction uniqueness (§1.1 minimum, §1.2 universal, §1.3 forced shape) |
| 01 | `01_notation_recursion.md` | The unavoidable recursion of notation (§2) |
| 02 | `02_statement.md` | The 4-clause axiom + axiom-vs-encoding-cost markers + what is **absent** (§3) |
| 03 | `03_form.md` | Why this form: austerity-as-audit; why 2 + binary; why symmetric + anti-reflexive (§4) |
| 04 | `04_falsifiability.md` | Derive-not-reconcile; §5.2.1 axiom-addition discard rule; 7 measurement falsifiers |
| 05 | `05_primacy.md` | Primacy as default structural position: every framework is a Lens reading of the same residue (§6) |
| 06 | `06_formalization.md` | Lean correspondence notes; axiom-corpus boundary; concrete numerics = Lens or forced (§7) |
| 07 | `07_self_reference.md` | No exterior; §8.4 dichotomy guide (re-read every Claude session) |
| 08 | `08_encoding_costs.md` | **§A appendix** — the four encoding costs of putting 213 on Lean 4 (inductive / cmp / canonical-subtype / ≠-precondition).  Why these are codomain costs, not axiom commitments.  Independent of §8 self-reference. |
| 09 | `09_chart_relativity.md` | Chart-local labels (§9.1, made explicit by `Lens/Number/Nat213/ChartGeneral`), operation/object non-separation (§9.2), flat ontology (§9.3, strict ∅-axiom reading), syntactic internalization (§9.4, full L2 + L3 realisation in `Lens/SyntacticInternalization`).  Lens-emergence vocabulary; cf. `research-notes/2026-05-18_lens_emergence_path.md`. |
| 99 | `99_history.md` | Change history of all absorbed sources |

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
- `seed/RESOLUTION_LIMIT_SPEC.md` — parametric `configCount`
  family spec (G120 Round 3 rewrite; `configCount 2 = 5²⁵`).
  Wins over any AXIOM/ chapter on resolution-limit topics.
- `seed/NOTATION.md` — symbol conventions.

## Möbius interpretation — canonical location

The 4-clause axiom admits the Möbius matrix `[[2, 1], [1, 1]]` /
iterator `P(x) = (2x+1)/(x+1)` interpretation.  **Canonical
treatment**: `02_statement.md §3.4`.  Other chapters reference §3.4
rather than duplicating.

Companion: `lean/E213/Lib/Math/Mobius213.lean` (7 ∅-axiom theorems —
discriminant, trace, det, Pell-Fib recurrences) and
`research-notes/archive/algebra_tower/G57_213_mobius_signature.md`
(multi-layer reading).

## Audit / implementation reference

Lean × axiom cross-check and faithful-emulator analysis live at
`lean/E213/AUDIT.md`.  Encoding-cost framing: `08_encoding_costs.md`
(why the costs exist).  Chart-relativity / flat-ontology framing:
`09_chart_relativity.md`.
