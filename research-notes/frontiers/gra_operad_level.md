# GRA operad level — the E_n-operad reading of Graded Residue Arithmetic

**Status**: open (conceptual model; no Lean at the operad level).  Recorded
per the `PROCESS.md` frontier-recording rule (named only in the
`theory/math/algebra/gra_book.md` tail / "Status: Conceptual model only. No
Lean formalization of operad level."; now tracked here).

## The open problem

GRA's five **Readings** (Sequence-length / Cochain-degree /
Truncation-level / **Operad-level** / Resolution-exponent) are free
Lens-presentations of the one forced P-orbit.  The **operad-level** reading
— "grade `n` = `E_n`-operad level", with the monoidal product
`M₁ ⊗_GRA M₂` (unit `trivial23`) — is presented at the *conceptual* level
in `gra_book.md` §3.4 (Reading₂ — Higher Algebra), with **no ∅-axiom Lean**
behind the operad structure.

## What IS closed (so the frontier is bounded)

- The GRA core (the `P = [[2,1],[1,1]]` graded arithmetic, grade =
  self-pointing depth) is ∅-axiom (Appendix B theorems verify).
- The other Readings have Lean anchors; the operad-level one does not.

## What is OPEN

A 213-native ∅-axiom formalization of the operad structure: the `E_n`
grading as a residue-self-pointing depth, the monoidal product
`⊗_GRA` with `trivial23` as unit, and the coherence (associativity /
unit) laws — built from the distinguishing, not imported from classical
operad theory.

## Cross-refs

- `theory/math/algebra/gra_book.md` — the book chapter (§3.4 operad reading)
- `theory/essays/gra/gra_universality_one_principle.md` — GRA as one principle
- `research-notes/frontiers/simplicial_operation_tower.md` — the operation tower
