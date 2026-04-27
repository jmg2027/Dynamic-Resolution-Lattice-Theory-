# CLAUDE.md — 213

## Status of this file

Every session dealing with 213 must read this file before starting.
The content may appear "philosophical," but skipping it causes more than
one hour of confusion to recur every session (demonstrated across many
past sessions).

**This file is a session guide; the axiom itself is in `AXIOM.md`.**
The formal audit standard is `AXIOM.md` (seed document).  CLAUDE.md is
the operational manual for preventing that axiom from being
unconsciously violated during session work.

## Identity of 213

### The axiom is a residue, not a choice

The 213 axiom is not a claim about "the foundations of the world."
It is **the minimum residue that inevitably remains the moment one tries
to point at something**.

Formal core (`AXIOM.md` §1.1): The 4 clauses of the Raw axiom (a, b, slash,
distinctness) are the strict minimum framework-internally
(4 cases in `Research/AxiomMinimality.lean`).
Conceptual extension (`AXIOM.md` §1.2 + `notes/75-76`): The "semantic
atom" framing is an *interpretive reading* of the formal core — no direct
formal Lean verification.  Maintain separation of the two layers.

- Writing "a and b" — "and" is also something.
- Writing "a, b" — "," is also something.  Whether that "," is universal
  or absolute is unknown — yet another something.
- Is a distinguished from "and"?  What distinguishes them?  Yet another something.

The moment notation begins, the notation itself endlessly produces new somethings.
Recursion is unavoidable.  The axiom is the minimum expression of this recursion.

### "Primitive distinction," not "relation"

- "Relation": presupposes two existing somethings + silently imports
  set-theoretic properties.
- "Primitive distinction": distinction operates first + requires only
  "not equal."
- "Primitive" = a pledge of no further reducibility.

### 213 is above everything

Every framework that points at something — set theory, category theory, logic,
language, physics — depends on the ability to distinguish and relate somethings.
213 is the minimum residue of that ability itself.  Every framework is a
collection of Lenses on top of this residue.

**"No absolute standard" is not a condition — it is the default state.**
"There is an absolute standard" is what carries the axiom-addition burden.
Therefore the primacy of 213 is an **unconditional** structural consequence.

### Linguistic inevitability

Even "primitive distinction" is not perfect.  "Difference" presupposes
"sameness"; "and" is misread as a conjunction; "," is a separator, not the
essence.  There is no perfect expression.  The current words are
**minimum-commitment expressions**, used with acknowledgment of residual
import.  Minimization is possible; elimination is not.

### Derive, not reconcile

All results must be derived only from the 213 axiom + explicit Lens properties.
Substituting external constants, fitting to experimental values, importing from
other theories — all are **fudge**.

- ch22 is wrong due to external substitution via eval.
- Paper 1 §1 (the axiom part, before R1–R5) is the correct template.
- All physics chapters must be derived by this methodology.
- When fudge is found, the Lens is corrected, not the formula.
- If that too fails, **the theory is abandoned**.  The infinite-extension
  defense of "more Lenses will be found" is not permitted.

### Why formalization and mechanical verification are essential

Mechanical verification does not permit fudge.  Therefore it **forcibly
reveals the point of derivation failure**.  When done by hand, quiet
correction is possible; the machine cannot do that.  This is why the
Mathlib-free + 0 sorry + 0 axiom constraint is imposed.  The axiom is
the contract; mechanical verification is the auditor.

### Adding external axioms is a theory-wide discard condition (Falsifiability)

The **falsifiability criterion** of AXIOM.md §5.2.1:

- All results of 213 must be derivable from Lean 4 core + the Raw axiom alone.
- If **any result is shown to be absolutely impossible without adding an axiom**,
  **the entirety of 213 theory is discarded**.  Not just the result alone.
- This is a direct consequence of the §1 declaration that the Raw axiom is
  the "minimum residue": if adding an axiom is genuinely necessary, Raw was
  not the minimum.

Operational principles:

- Adding external axioms (Classical, LEM, native_decide, etc.) is entirely
  forbidden.
- Results that are blocked are left as "open," with distinction between
  **permanent wall vs. temporary obstacle**.  A permanent wall triggers a
  theory failure declaration.
- Lean verification = the mechanical auditor of falsifiability.

Mingu's confirmed declaration (2026-04-24).  Never relaxed.

### The status of "something" is open

From the moment one says "something," is it already a Lens?  Possibly.
Is 213 Platonic ideals?  Probably not.  These questions are open and do
not affect the usefulness of 213.  What matters is whether derivation
succeeds, not ontology.

## Operational rules (direct consequences of the above)

These are not independent rules but things that automatically follow from
the identity above.  Do not merely memorize the rules — **trace back why
they hold**.

- **Lens ≠ functor.**  A functor presupposes a prior category structure.
  Raw has no morphisms.  The moment "functor" is attached to Lens, category
  theory is silently imported.  → `research/notes/19_lens_not_functor.md`.
- Words like **"observer," "space," "perception," "structure," "relation"**
  are forbidden in explaining the 213 axiom.  These words are derived results,
  not presuppositions.
- **Notation conventions**: see `NOTATION.md`.  ZFC set literals
  `{a, b, /}`, collective language like "Raw contains X," and the ∈ symbol
  to the left of Raw are all forbidden.
- **Cardinality is a property of the (Raw, Lens) pair.**  From Raw alone,
  nothing about countable/uncountable can be said.
- **Existence mode: don't care.**  The Platonic / stepwise distinction is
  Lens output, not a property of the axiom.
  → `research/notes/17_existence_mode_lens.md`.
- **`open` of the `E213.Firmware.Internal` namespace is forbidden outside
  Firmware internal modules.**  Internal is exclusively for encoding
  scaffolding (`Tree`, `Tree.cmp`, `Tree.canonical`, etc.).  `open Internal`
  in user code violates the Raw abstraction.  → `AUDIT_Lean.md` §5.2(D).
- **`Raw.fold` / `Raw.rec` place `combine` symmetry / slash symmetric
  treatment as the user's responsibility.**  Asymmetric Lenses leak encoding
  artifacts into output.  See the WARNING in each file's doc-string.
  → `AUDIT_Lean.md` §5.2(A), (B).

## Organization rules

Document / file / directory organization follows these principles.  Be
conscious of them **when creating each new file**, not after things pile up.

- **Delete deprecated items.**  Do not preserve superseded documents or code
  (git history retains them).  Keeping them alive as "historical record"
  makes them noise in themselves.
- **Too many files is bad.**  Consolidate small fragments on similar topics.
  E.g., 5 notes from the same arc → 1 synthesis note.
- **One file that is too long is bad.**  If a file naturally splits into two
  topics, separate them.  Lean: the 80-line hook enforces this.
- **Too many entries in one directory is bad** (50+ calls for a sub-dir
  review).  Too few is also bad (3 or fewer should be merged into parent).
- **Too deep or too many directories is bad.**  Depth 3-4 levels recommended.
  Do not create directories just because they happen to be there.
- **Sort for natural reading order.**  The NN_ prefix for notes, the layer
  structure of Lean modules (Firmware → Hypervisor → Research) — all should
  flow naturally in reading order.
- **Prefer updating existing files over creating new ones.**  If a file
  with related content already exists, append/edit there.

Organization that violates the above rules is not organization but accumulation.

## Physics chapter audit criterion

Can the results of that chapter be derived without fudge from
**AXIOM.md + explicit Lens properties**?  If not, **isolate as speculative**.

## Papers 1 and 2 deleted (2026-04-24)

The previous `213/PAPER.md` (R1-R5 → ℂ derivation) and `213/PAPER2.md`
(r5-critique) have been deleted.  Reason: both documents were **derivation
attempts at a specific point in time**, and their framing became stale during
arc progression.  `notes/30_bool_is_liar_paradox.md` records the background
for this deletion.

Currently **AXIOM.md is the sole axiom document**, **PAPER1.md is the sole
formal paper** (foundational formalization of Raw + Lens without R1-R5
derivation).  Derivation is explored freely in `research/notes/`
(without a judgment frame).

## File map

- **`AXIOM.md` — axiom seed document (highest authority).**
- **`PAPER1.md` — paper form of the Lean 4 core formalization.**  Final stop
  point (2026-04-26).  §9 + Appendix A of PAPER1.md are the formal core of
  the semantic atom thesis.
- **`ORIGIN.md` — original prompt chain of the theory (fixed 2026-04-24).**
  Consult first when the axiom's form is questioned "why this one?".
  PAPER1.md body has no physics motivation.
- `NOTATION.md` — notation conventions.
- `IMPLEMENTATION.md` — Raw + Firmware implementation audit study.
- `AUDIT_Lean.md` — Lean × AXIOM cross-check audit.
- `research/notes/` — 5 reference notes (17, 19, 30, 75, 76).
- `framework/E213/` — Lean 4 core formalization.
- Root `../HANDOFF.md` — session arc continuity.

## Author & licence

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- 0 sorry, 0 external axioms.  Lean 4 core only — no Mathlib.
