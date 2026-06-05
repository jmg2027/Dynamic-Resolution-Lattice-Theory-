# Two kinds of proof-ISA content: lifts versus fold-equalities

A structural observation that sharpens what the proof-ISA is, and resolves a
question the cross-domain compilation leaves open.

## The split

The lift catalog (`lean/E213/Lib/Math/Foundations/ProofISALifts.lean`) records
seven **lift** archetypes — DIAGONAL, LOOP, ORBIT, REFRAME, COUNT, FLOW,
POSITIVITY.  Every one answers the same question: *how does a fact true on each
finite sample become true uniformly?*  The open-problem difficulty of a conquest,
once compiled, lives in its **finite → uniform lift**.

But a second, different kind of conquest keeps appearing, and it is **not a
lift**.  It is a **fold-equality** (EQUIV): two readings of one object — two
Lenses, two folds `Raw → α` — give the *same* value.  Examples in the repo:

- **Pick** (`Geometry.PickTheorem`): the lattice-point-count fold equals the area
  fold.
- **Heron** (`Algebra.CrossDomainIdentities`): the side-product fold equals the
  `16·Area²` fold.
- **Euler four-square / Cauchy–Schwarz** (`CrossDomainIdentities`, `Positivity`):
  one bilinear reading equals another.

These are equalities of two readings, with no "finite sample → uniform" content.
That is exactly why `ring_intZ` (or `decide`) closes them *instantly* — and why
they *feel* slighter than a lift: **their lift-difficulty is zero**.

## Where the difficulty of an EQUIV conquest actually lives

A fold-equality is cheap or century-hard depending on **one** thing: the cost of
*constructing the second fold* — the cross-domain bridge.

- Pick, Heron: the second fold is elementary algebra, ready to hand → the
  equality is a one-line ring identity.
- **Weil conjectures** (point-count fold equals the étale-cohomology fold),
  **Atiyah–Singer** (analytic index equals topological index), **geometric
  Langlands** (two categories agree): the second fold had to be *built* (a whole
  cohomology theory, a whole category).  *That* construction is the conquest; the
  equality, once both folds exist, is comparatively formal.

So EQUIV's difficulty is **orthogonal** to lift-difficulty: it is bridge-
construction cost, not finite→uniform cost.  This is the precise reason the
`ring_intZ` cross-domain identities, though genuine, carry a different texture
than FLOW driving Ricci or ORBIT localizing Markov: those have lift content; the
identities have only (ready-to-hand) bridge content.

## Resolution of the EQUIV question

Is EQUIV an eighth lift archetype, or REFRAME's terminal case?  Neither.

- It is **not REFRAME**: REFRAME *exploits a difference* between two folds (read
  through the presentation whose fiber is smaller, where SEPARATE fires).  EQUIV
  *asserts agreement* between two folds.  Opposite uses of the second fold.
- It is **not a lift archetype**: it has no finite→uniform content, so it does
  not sit beside the seven in the lift catalog.

EQUIV is a **different category of ISA content** — the *identity* category, beside
the *lift* category.  It is exactly the GRA-universality target
(`blueprints/math/16_gra_universality.md`, "the 5 Reading isomorphism"): *distinct
Lens readings of one residue coincide.*  The seven lift archetypes are complete
**as lifts**; EQUIV is the heading of the orthogonal axis.

## A bonus: mex is GAP

One more ISA reading, from the game-theory thread.  The Sprague–Grundy value of
an impartial game is `grundy = mex {grundy of each option}`, where `mex` (minimal
excludant) is the least natural the option-set omits
(`Combinatorics.SubtractionGame.mexPair`, `grundy`).  `mex` *is* the **GAP**
instruction read by "least": GAP is "the reading does not cover its codomain; the
un-covered surplus is the residue," and mex points at that surplus by its
smallest witness.  Sprague–Grundy is then "every impartial game **compiles** to a
nimber via iterated GAP," and games of equal Grundy value are interchangeable — a
COMPILE/READ universality.  So the game-theory conquests are genuine ISA content
(GAP + backward-induction LOOP), not fold-equalities — which is why they read as
more substantial than the `ring_intZ` identities.

## Summary

| ISA content | question answered | difficulty lives in | cheap when | example |
|---|---|---|---|---|
| **Lift** (7 archetypes) | finite → uniform? | the lift | — | FLT, Markov, Ramsey, Ricci |
| **Fold-equality** (EQUIV) | do two folds agree? | constructing the 2nd fold | 2nd fold ready | Pick, Heron; (hard) Weil, Langlands |

The proof-ISA therefore has two orthogonal axes, not one list; "compile a
conquest" means locating it on *both*.
