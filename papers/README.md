# papers/

Self-contained paper-form expositions written for readers outside the
project — working mathematicians who want the result and its
verification without first absorbing the full 213 corpus.

Each paper states its theorems precisely, names the machine-checked Lean
module behind every numbered result, and gives a reproduction protocol.
The narrative source of truth remains `theory/` (which mirrors
`lean/E213/` by path); a paper is a *reading* of that corpus for an
external audience, not a replacement for it.

## Contents

- `the_residue_of_distinguishing.md` — **The Residue of Distinguishing.**
  The spine, not a survey: a single argument carried from one primitive
  (distinguishing) through the one theorem it forces (the residue, a
  faithful-but-never-total self-cover), the no-exterior closure, the
  four-clause Raw, the forced `(N_S,N_T,d)=(3,2,5)`, the `⟨C|L⟩⊕Residue`
  calculus, the cross-route-agreement signature of breadth, and the
  empty-axiom contract. Where `the_213_programme.md` catalogues what the
  residue rebuilds, this paper proves the one thing the catalogue rests on.
  Every citation is a verified ∅-axiom theorem.

- `the_213_programme.md` — **The 213 Programme: Mathematics from the
  Residue of Distinguishing.** The flagship survey for mathematicians: the
  residue-as-theorem, the four-clause Raw axiom, three-direction
  uniqueness fixing `(N_S,N_T,d)=(3,2,5)`, the decomposition calculus
  `⟨C|L⟩⊕Residue` with Raw as initial object, the axiom-free
  reconstruction of the number systems / algebra towers / cohomology / GRA
  universality (Cat and HoTT as readings), the boundaries chapter, and the
  empty-axiom falsifiability contract with the physics deployment stated
  honestly.

- `no_walls_only_parameters.md` — **No Walls, Only Free Parameters: A
  Decomposition Calculus for the Boundaries of Mathematics.** The
  tetrachotomy `∅/0/1/many = absence/wall/forced/free` as the
  section-count of a reading-fibration; choice/forcing/large-cardinals as
  free parameters; the one Lawvere wall (Cantor/Russell/Gödel/halting/
  generic); the self-grounding theorem and the idempotent fixed point.
  Backed by nine ∅-axiom modules in `lean/E213/Lib/Math/Logic/`.
