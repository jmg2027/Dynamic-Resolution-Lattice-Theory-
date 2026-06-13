# Slot Arithmetic — number systems from the sorted list

**The third volume (준-책): rebuilding the number tower from ℕ-slots
alone, with no inverse operation, no quotient, and no axiom.**

Mingu Jeong — theory.  Formalization, audit, and adversarial
cross-examination by Claude (Anthropic); see Acknowledgments.
All cited theorems are machine-checked in `lean/E213/`, ∅-axiom
(no `propext`, `Quot.sound`, `Classical.choice`, `native_decide`,
`sorry`; verified by `tools/scan_axioms.py`).

---

## Abstract

> "연산(자연수,자연수) → 자연수 인 연산들로 결합된 자연수 슬롯들로
> 자연수 자유도를 통해 수체계를 만든다" — *number systems are built
> from ℕ-slots combined by (ℕ,ℕ)→ℕ operations, through ℕ degrees of
> freedom alone.*

Start from the naturals as a sorted list — unit-started, unit-spaced —
and admit only total operations `(ℕ,ℕ) → ℕ`.  Never subtract, never
divide, never adjoin.  Ask questions instead: `a + x = b`, `a·x = b`,
`x^(c,d) = (a,b)`.  Where a question has no answer on the list, **the
question's own slot tuple is the new number**.

This volume shows that the entire classical tower — the negatives,
the rationals with their signs and their order, √2, the imaginary
unit — arises this way, as *addresses in slot space*, with the
classical systems' familiar presentations exposed as optional
flattening readouts: lowest terms, canonical remainders, the very
equality sign.  The two routes to the rationals commute because
distributivity *is* the commutation law of the two pair-Lenses
(`Rat213.square_commutes`).  The imaginary unit requires no new
mechanism: `x² = −1` is a question whose slots already sit one layer
up, and `i` is to +-pair slots exactly what `√2` is to ×-pair slots —
sibling constants of sibling layers.

Beneath it all sits a property-free **witness layer** for an
arbitrary operation — tetration included — in which the classical
algebraic properties are revealed as job descriptions: commutativity
fuses the two questions an operation asks; cancellation *is* witness
uniqueness; the medial law alone makes products of witnesses witness
products.  The sorted list pays these prices itself for every
operation that only moves forward along it.

That every theorem here carries the empty axiom set is not a
technical feat bolted on: it is the ontology.  Total ℕ-operations in
witness form leave no seam for partiality, choice, or
proposition-extensionality to enter.

## How this volume relates to the other two

`books/lens-tower/` (The Lens Tower) *applies* the tower; `books/lens-tower/foundations/`
asks whether the tower is well-founded *as a tower*.  This volume
**rebuilds the tower from below**, so that the other two volumes'
object exists without ever having been postulated.

## Chapters

1. `01_the_list_and_the_question.md` — the sorted list; order as the
   +-witness question; the sandwich as the proper probe; equality as
   a manufactured artifact.
2. `02_pairs_are_numbers.md` — the tuple ontology: `(1,3)` is a
   two-axis number; relations, not identities; flattening as a Lens
   choice; what classical notation hides.
3. `03_the_witness_layer.md` — an arbitrary operation, every property
   forgotten: the bifurcating question, the witness relation, and the
   true jobs of commutativity, cancellation, and the medial law;
   progressive versus wrapping operations.
4. `04_two_transports_one_square.md` — the difference and ratio
   layers; sign and remainder as witness readouts; reduction as a
   possibility theorem; the signed rationals; the commuting square.
5. `05_layer_constants.md` — questions whose slots are pairs; √2 and
   i as siblings; the four-axis product; how a fiber transports
   instead of vanishing.
6. `06_boundaries.md` — fold-back and the algebraic/sandwich-family
   boundary; the interaction wall at tetration; wrapping as fiber
   readout; the open programme.
