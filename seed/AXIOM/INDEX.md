# seed/AXIOM/ — the axiom corpus

The 4-clause Raw axiom together with the chapters needed to
audit the axiom itself: what it is, why it has the form it has,
how its uniqueness is established, how it relates to other
frameworks, how it is falsified, and how it is mechanically
verified.

Lean implementation audit (faithful-emulator analysis,
device classification, axiom cross-check) lives at
`lean/E213/AUDIT.md`.

## Chapters

| # | File | What it covers |
|---|---|---|
| 1 | `01_residue.md` | What the axiom is — the minimum residue of pointing.  The unavoidable recursion of notation, primitive distinction, linguistic inevitability, the status of "something." |
| 2 | `02_axiom.md` | The axiom itself — language used, the minimum-commitment statement, self-completion, the code-friendly four-clause restatement, what is absent. |
| 3 | `03_form.md` | Why this form — austerity as audit, why two + binary, why symmetric + anti-reflexive, the forcing chain 1 → 2 → 3 → 4, the Möbius algebraic signature. |
| 4 | `04_uniqueness.md` | Three-direction uniqueness — from below (clause removal collapses), sideways (any framework factors through Raw), from above (forced shape `(NS, NT, d) = (3, 2, 5)`), bundled. |
| 5 | `05_no_exterior.md` | No exterior — circularity as structural closure, redefining "derive," the dichotomy-avoidance guide, self-completion, the Möbius model, frozen + dynamic readings. |
| 6 | `06_lens_readings.md` | Lens readings of the same residue — chart-local labels, operation/object non-separation, flat ontology, syntactic internalisation, K_∞ ≡ point at raw level. |
| 7 | `07_primacy.md` | Primacy and the direction of derivation — every framework as a Lens reading, derive-do-not-reconcile. |
| 8 | `08_falsifiability.md` | The ∅-axiom contract — mechanical verification, internal falsification, empirical predictions, the measurement-falsifier table, formal guarantees. |
| 9 | `09_lean_correspondence.md` | The faithful Lean emulator, three-direction uniqueness bundled, realisations of the doctrinal chapters, corpus boundary, concrete numerics. |
| 10 | `10_encoding_costs.md` | **Appendix** — the four encoding costs of putting 213 on Lean 4 (inductive / cmp / canonical-subtype / ≠-precondition), the faithful-emulator claim, cmp-independence. |
| 99 | `99_history.md` | Change history. |

## How to read

  - **First time**: read `seed/INDEX.md` — it is self-contained
    with the axiom + key concepts + falsifiability rule on one
    screen.
  - **For axiom understanding**: §2 → §3 → §1.  The statement
    first, then why this form, then the framing of the
    framework.
  - **For Claude session start**: §5.4 (the dichotomy guide) is
    the high-priority refresh, per `CLAUDE.md` boot sequence.
  - **For the falsifiability rule**: §8.2.  The discard
    condition (§8.5) and the precision side (§8.6) follow.
  - **For Lean implementation audit**: `lean/E213/AUDIT.md`
    together with §10.

## Cross-references at seed/ root

  - `seed/INDEX.md` — standalone entry point.
  - `seed/ORIGIN.md` — DRLT origin narrative.
  - `seed/NOTATION.md` — symbol conventions.
  - `seed/CLOSED_FORM_SPEC.md` — closed-form catalogue +
    Bishop subsumption.
  - `seed/THEOREM_METHODOLOGY_SUITE.md` — proof-shape fingerprint
    (§TH-1), Raw-derivation three readings (§TH-2), falsifier
    surface (§TH-3), L1 parametric methodology (§TH-4).
  - `seed/META_SCAN_ARCHETYPES.md` — 11 scanner archetypes +
    dual-branch process model.

## Möbius signature — canonical location

The 4-clause axiom admits the Möbius matrix `[[2, 1], [1, 1]]`
and iterator `P(x) = (2x + 1) / (x + 1)`.  Canonical treatment:
§3.5.  §5.6 records the dual reading (frozen fixed point +
dynamic convergence) as the concrete model of self-reference.

Companion: `lean/E213/Lib/Math/Algebra/Mobius213.lean` (∅-axiom
theorems: discriminant, trace, det, Pell-Fib recurrences).
