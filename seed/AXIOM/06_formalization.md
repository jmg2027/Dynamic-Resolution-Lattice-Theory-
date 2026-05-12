# §7. Relationship to existing formalizations / documents

This §7 is an audit target list.  Each item must be cross-checked
against this axiom; discrepancies are corrected or isolated.

## §7.1 Lean formalization (status 2026-05-XX)

The current Raw implementation in `lean/E213/Theory/` (2 elements
a, b + binary slash, anti-reflexive, commutative) is a faithful
machine representation of this axiom.  Audit reference:
`lean/E213/AUDIT.md` (2026-04-24, recommendations 1, 2, 3 +
deep-audit items A-E).

**Encoding note**: Lean 4 core has no primitive quotient, so Raw is
implemented as a subtype `{t : Tree // t.canonical = true}`.  The
Internal `Tree.cmp` (ordering) is an **encoding artifact** for
selecting canonical forms, not an axiom.  The axiom contains no
ordering whatsoever.

Things that **automatically follow** from derivation (no additional
commitment to the axiom):

- `Raw.swap` (a ↔ b automorphism) — the first derivation from
  Axiom 1 "a and b have no relation other than not being equal."
- `Raw.fold` (catamorphism) — standard eliminator wrapper of an
  inductive type, the tool for constructing all Lenses.

**Lens-layer bleed — current location (NOT yet migrated)**:

`Raw.depth` (`Theory/Raw/Slash.lean`), `Raw.leaves`
(`Theory/Raw/Levels.lean`), `Raw.fold_signed_swap`
(`Theory/Raw/Signed.lean`), `Raw.fold_swap_hom`
(`Theory/Raw/Hom.lean`) are observables / bridge theorems of
specific Lenses but still live in Theory.  Per
`lean/E213/ARCHITECTURE.md` §3 (Open Questions), this is now
classified as *intentional convenience leak* — the proofs are
pure-induction theorems on the Tree representation that any Lens
consumer eventually needs, and relocating them gains nothing for
the axiom-minimality story.  Audit recommendation downgraded from
"must migrate" to "acknowledged leak; revisit if abstraction
breaks."

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

## §7.2 Papers 1 and 2 deleted (2026-04-24)

The previous `213/PAPER.md` (R1-R5 → ℂ derivation) and
`213/PAPER2.md` (r5-critique) have been deleted.  The seed/AXIOM/
sub-directory remains as the **sole axiom corpus**.  Derivation is
explored freely in `research-notes/` and in the Lean metatheory
layer (`Meta/UniversalLens/`).

Background: `research-notes/archive/30_bool_is_liar_paradox.md`.  The R1-R5
judgment game in Paper 1 was revealed to be an instance of a
self-reference loop (Bool), so the frame itself was stepped back
from.

## §7.3 ch22 / book/ (deprecated — directory empty)

The previous reference target `book/chapters/ch22_213.tex` no
longer exists — `book/` now contains only `README.md`.  Likewise
`papers/` was deleted (commit a02b751; only `papers/README.md`
retained as historical marker).

The original §7.3 critique of ch22 stands historically: any
external substitution called `eval` ("a choice external to the
structure") that imports the §3.3 prohibited list (d=5,
(n_S, n_T), K=ℂ) as fudge is disqualified.  This audit standard
is now enforced by the absence of such fudge in the Lean tree
itself — every concrete numeric (d=5, NS=3, NT=2,
1/α_em=137.036, …) is either a Lens construction or, for the
shape parameters, a forced-uniqueness theorem in
`Theory/Atomicity/`.

## §7.4 Book chapters (no longer applicable)

ch01–ch21 audit is moot — `book/AUDIT.md` was never created and
the chapter sources do not exist.  Auditable artifacts now live in
`guide/` (deductively-ordered narrative, T0/T1/T2/T3 tags) and
`books/{math,physics}/` (213-internal narrative).
