# §7. Relationship to existing formalizations / documents

This §7 is an audit target list.  Each item must be cross-checked
against this axiom; discrepancies are corrected or isolated.

## §7.1 Lean formalization

The current Raw implementation in `lean/E213/Theory/` (2 elements
a, b + binary slash, anti-reflexive, commutative) is a faithful
machine representation of this axiom.  Detailed device-by-device
classification (α/β/γ/δ) + axiom × Lean cross-check:
`lean/E213/AUDIT.md`.

**Encoding note**: Lean 4 core has no primitive quotient, so Raw is
implemented as a subtype `{t : Tree // t.canonical = true}`.  The
Internal `Tree.cmp` (ordering) is an **encoding artifact** for
selecting canonical forms, not an axiom.  The axiom contains no
ordering whatsoever.  Cmp-independence is mechanically verified at
`lean/E213/Theory/Internal/RawCmpIndependence.lean`.  Full encoding-
cost catalog: `08_encoding_costs.md`.

Things that **automatically follow** from derivation (no additional
commitment to the axiom):

- `Raw.swap` (a ↔ b automorphism) — the first derivation from
  Axiom 1 "a and b have no relation other than not being equal."
- `Raw.fold` (catamorphism) — standard eliminator wrapper of an
  inductive type, the tool for constructing all Lenses.

**Lens-layer bleed** (Theory currently holds some Lens-flavored
observables): `Raw.depth` (`Theory/Raw/Slash.lean`), `Raw.leaves`
(`Theory/Raw/Levels.lean`), `Raw.fold_signed_swap`
(`Theory/Raw/Signed.lean`), `Raw.fold_swap_hom` (`Theory/Raw/Hom
.lean`).  Classified as *intentional convenience leak* — these are
pure-induction theorems on Tree that every Lens consumer eventually
needs, and relocating gains nothing for axiom-minimality.

**Forced shape uniqueness**: see `00_nature.md` §1.3.
`Theory/Atomicity/*` proofs (arity = 2, atomic ⇒ d = 5,
(NS, NT) = (3, 2)) are pure-ℕ propositions that *do not import*
Raw.  They sit in Theory structurally — they are part of "what
Raw must look like" — but their dependency on Raw is zero.

**Universal-Lens metatheory**: see `00_nature.md` §1.2 cross-ref.
`Meta/UniversalLens/{Core, Nat2Inj, Q213Inj, Nat3, Nat4, Q213_3,
TripleCapstone, Padding, PaddingCapstone}` formalize the "any
distinguishability framework factors through Raw" obligation.
Together with §1.3 these close axiom-uniqueness in three directions
(below/sideways/above).

## §7.2 Deleted paper drafts

- `seed/PAPER1.md` (1377 lines, archival seed paper) — deleted
  2026-05-12.  Historical citations in Lean docstrings
  (`PAPER1 §X.Y`, ~25 files) remain as narrative references with
  no live target.
- `213/PAPER.md` (R1-R5 → ℂ derivation), `213/PAPER2.md` (r5-
  critique) — deleted 2026-04-24.  Background:
  `research-notes/archive/30_bool_is_liar_paradox.md` (the R1-R5
  judgment game was revealed to be a self-reference loop on Bool).
- `papers/` directory: only `papers/README.md` retained as historical
  marker; original paper sources deleted (commit a02b751).

The seed/AXIOM/ sub-directory remains as the **sole axiom corpus**.
Derivation is explored freely in `research-notes/` and in the Lean
metatheory layer (`Meta/UniversalLens/`).

## §7.3 Book / chapter audit (no longer applicable)

The previous reference target `book/chapters/ch22_213.tex` no
longer exists.  `book/` was emptied; new authoritative narratives
now live in:

- `guide/` — deductively-ordered narrative (T0/T1/T2/T3 tags)
- `books/{math,physics}/` — 213-internal narrative

The historical critique of ch22 (external `eval` substitution
importing the §3.3 prohibited list as fudge) is enforced
mechanically in the current Lean tree: every concrete numeric
(d=5, NS=3, NT=2, 1/α_em=137.036, …) is either a Lens construction
or, for the shape parameters, a forced-uniqueness theorem in
`Theory/Atomicity/`.
