# §99. Change history

A consolidated change log for the axiom corpus.  Includes the
deprecated R-frame note that earlier sessions referenced.

## §99.A Deprecated R1–R5 naturalness frame

Earlier drafts introduced an **R1–R5 judgment-game frame** as a
"naturalness" criterion for Lens choice.  The frame was stepped
back from after `research-notes/archive/30_bool_is_liar_paradox.md`
revealed that R1–R5 is a self-reference loop on `Bool`; the
frame itself fell.

The current uniqueness story does NOT route through R1–R5:

  - **Universal-Lens claim** (§4.2): any distinguishability
    framework factors through Raw.  No R-game required.
  - **Atomicity claim** (§4.3): Raw's shape is forced to
    `d = 5`, `(NS, NT) = (3, 2)` structurally — see
    `Theory/Atomicity/Five.lean` and the related Atomicity
    cluster.
  - **Resolution-limit family readout**
    (`seed/RESOLUTION_LIMIT_SPEC.md` §2): `configCount 2 = 5²⁵`
    as one value of the parametric Lens-output family
    `configCount : Nat → Nat`.  An earlier "4-way convergent
    invariant" framing was retracted (only 2 of 4 readings had
    real Lean derivations).

ℂ enters downstream as a Lens construction
(`Lib/Math/CayleyDickson/`), NOT as a consequence of any R1–R5
axiom set.

### Typeclass rename in `Meta/SelfRecognising.lean`

The typeclass hierarchy was renamed to drop the historical
R-prefix while preserving semantics:

| Earlier (R-frame)        | Current (descriptive)          |
|--------------------------|--------------------------------|
| `R12Codomain`            | `CommBinaryCodomain`           |
| `R3Codomain`             | `NonVanishingCodomain`         |
| `R4Codomain`             | `ConjugationCodomain`          |

Companion macros, tactics, filenames, and theorem prefixes
(`r4_conj_*` → `conjugation_*`) were renamed in lockstep.  The
content (commutative combine, no-zero-divisors, swap-matching
involution) is independent of the R-frame and is used as a
generic codomain spec.  Five files consume it (CayleyDickson
Z2 / ZOmega / ZI / ZSqrt instances + CUniquenessBridge); all
updated, build clean, axiom scan unchanged.

---

## §99.B Change log

### Corpus rewrite (2026-05-22)

Full rewrite of the axiom corpus from the original 11-chapter
layout into a 10-chapter natural-narrative arc, with file names
matching chapter numbers (file `0N_*.md` carries §N):

  · `01_residue.md` (§1) — what 213 is.  Combines the earlier
    `00_nature.md` §1.0 (position / vocabulary) with
    `01_notation_recursion.md` (§2) as §1.2.
  · `02_axiom.md` (§2) — the 4-clause statement + what is
    absent.  Was `02_statement.md`.
  · `03_form.md` (§3) — why this form; absorbed the Möbius
    signature from the earlier §3.4.
  · `04_uniqueness.md` (§4) — three-direction uniqueness.
    Extracted from the earlier `00_nature.md` §§1.1 + 1.2 + 1.3.
  · `05_no_exterior.md` (§5) — self-reference + dichotomy
    guide.  Was `07_self_reference.md`.
  · `06_lens_readings.md` (§6) — Lens readings (chart, flat
    ontology, syntactic internalisation, K_∞ ≡ point).  Was
    `09_chart_relativity.md`.
  · `07_primacy.md` (§7) — primacy + derive-not-reconcile.
    Was `05_primacy.md`; absorbed the earlier `04_falsifiability.md`
    §5.1 (derive-not-reconcile).
  · `08_falsifiability.md` (§8) — ∅-axiom contract + measurement
    falsifiers.  Was `04_falsifiability.md` (without §5.1).
  · `09_lean_correspondence.md` (§9) — Lean correspondence.  Was
    `06_formalization.md`.
  · `10_encoding_costs.md` (§10) — appendix.  Was
    `08_encoding_costs.md` (§A).

The chapter renumbering re-aligns file numbers with §-numbers
and makes the reading order match the natural narrative arc
(residue → axiom → form → uniqueness → no-exterior → Lens
readings → primacy → falsifiability → Lean correspondence →
appendix).  External cross-references across the repo
(`README.md`, `CLAUDE.md`, `HANDOFF.md`, `STRICT_ZERO_AXIOM.md`,
catalogs, theory chapters, `lean/E213/*.lean` docstrings, etc.)
were updated by script.

### Earlier history

  - **2026-04-24**: initial AXIOM corpus drafts.  Session
    `claude/lean-infinity-explanation-QqnSp`.
  - **2026-04-24 (2nd)**: §7 (Lean formalisation, now §9)
    reinforced.  Applied recommendations from the original
    `AUDIT_Lean.md`.
  - **2026-04-24 (3rd)**: added §8 (self-reference, now §5) +
    §9 (naturalness, R1–R5 motivation; later deprecated —
    §99.A).  Recorded that dichotomies like "is Lens inside or
    outside the axiom?" are mistaken.
  - **2026-05-05**: §99.A typeclass rename executed.
    `Meta/SelfRecognising.lean`'s `R12Codomain` / `R3Codomain`
    / `R4Codomain` → `CommBinaryCodomain` /
    `NonVanishingCodomain` / `ConjugationCodomain`.  Companion
    macros, tactics, filenames, theorem prefixes renamed in
    lockstep across 16 files.  Build clean, axiom scan
    unchanged.  Architectural reference:
    `lean/E213/ARCHITECTURE.md`.
  - **2026-05-XX**: major theory-development pass.
      · added §1.3 / §4.3 "Forced shape uniqueness" —
        `Theory/Atomicity/*` proofs formalise the third pillar
        of axiom uniqueness (above), alongside §1.1 / §4.1
        (below) and §1.2 / §4.2 (sideways).
      · §1.1 / §4.1 reinforced with cross-reference to
        `Meta/UniversalLens/` family.
      · §1.2 / §4.2 path corrections:
        `Research/NoDepthParity.lean` →
        `Lens/Morphism/{NoDepthParity, DepthParityNotFold}.lean`.
      · §7.1 / §9.1 updated: Lens-layer bleed migration
        deprioritised.
      · §7.3, §7.4 obsoleted: legacy `book/chapters/*.tex` and
        `book/AUDIT.md` no longer exist.
      · §9 substantially rewritten as §99.A: the R-game
        judgment frame is stepped back from.  The current
        uniqueness story is Universal-Lens + Atomicity +
        Resolution-limit (`configCount` parametric family;
        N_U re-derivation Round 3 retracted the "4-way invariant
        N_U" framing).

### Earlier draft consolidations

The original drafts (`AXIOM.md`, `PHILOSOPHY.md`,
`FALSIFIABILITY.md`, `IMPLEMENTATION.md`, `AUDIT_Lean.md`,
`PAPER1.md`) were initially separate files at `seed/` root.
They were consolidated into the chapter sub-directory
`seed/AXIOM/`:

  · `AXIOM.md` and `PHILOSOPHY.md` → `01_residue.md` (§1) +
    `02_axiom.md` (§2) + `03_form.md` (§3).
  · `FALSIFIABILITY.md` → `08_falsifiability.md` (§8).
  · `IMPLEMENTATION.md` + `AUDIT_Lean.md` →
    `09_lean_correspondence.md` (§9) + `10_encoding_costs.md`
    (§10).
  · `PAPER1.md` was deleted (2026-05-12).

`seed/INDEX.md` was rewritten as the standalone entry point
(4-clause axiom + key concepts + falsifiability rule visible
in one screen).  Authority documents (`ORIGIN.md`,
`RESOLUTION_LIMIT_SPEC.md`, `NOTATION.md`) remained at `seed/`
root.

## Author & licence

  - Author: **Mingu Jeong** only.  Claude in acknowledgements.
  - 0 sorry, 0 external axioms.  Mathlib-free.

## 2026-06-02 — §6.7 sign-Lens refinement

§6.7's "adding a sign-Lens gives ℤ" sharpened: the sign-Lens named
concretely as the count-Lens on an *ordered* count-pair `(m,n) ↦ m−n`
(magnitude Nat-style, sign Bool-style §5.2; orientation = §2.4 clause-3
direction-freedom broken), grounded in `Int213`'s `subNatNat` pair-arithmetic.
Refinement, not a new chapter — ℤ-as-Lens-output was already foundational in
§6.7.  Essay: `theory/essays/integers_as_difference_lens.md`.
