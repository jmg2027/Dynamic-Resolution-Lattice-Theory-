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

- `no_walls_only_parameters.md` — **No Walls, Only Free Parameters: A
  Decomposition Calculus for the Boundaries of Mathematics.** The
  tetrachotomy `∅/0/1/many = absence/wall/forced/free` as the
  section-count of a reading-fibration; choice/forcing/large-cardinals as
  free parameters; the one Lawvere wall (Cantor/Russell/Gödel/halting/
  generic); the self-grounding theorem and the idempotent fixed point.
  Backed by nine ∅-axiom modules in `lean/E213/Lib/Math/Logic/`.
