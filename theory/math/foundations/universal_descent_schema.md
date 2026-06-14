# The universal descent schema — A6 FLOW as the normal-form lift

## Overview

A recurring shape across the corpus: a *reduction* carries a `Nat`-valued
**monovariant** that strictly drops off a **normal form**, and the reduction
**preserves an invariant** — so every object reduces in finitely many steps to a
normal form, on which the invariant reads off the answer.  This is the **A6 FLOW**
archetype, originally stated for a self-map and read as the discrete sibling of
Ricci flow.  The schema below widens it to a reduction **relation** and shows it
is the *universal* descent/normal-form lift: GCD, UFD separation, Markov
reachability, and discrete Ricci flow are all instances of one ∅-axiom generator.

The content is not a new hard theorem — it is a *recognition*: four genuinely
independent descents (none importing the others) re-prove the same
fuel-recursion-on-a-monovariant, and that common skeleton is one Lean object.

## Lean source

- Umbrella / generator: `lean/E213/Lib/Math/Foundations/MonovariantFlow.lean`
  (19 PURE) — `Reaches`, `descent_reaches_fueled`, `descent_reaches`,
  `reaches_invariant`, `descent_invariant`, `flow_reaches_of_relation`,
  `euclid_via_descent_invariant` (+ the self-map `flow_reaches` and the GCD flow).
- Instance (UFD): `lean/E213/Lib/Math/Foundations/VpSeparationDescent.lean` (6 PURE).
- Instance (Markov): `lean/E213/Lib/Math/NumberSystems/Real213/Markov/MarkovDescentSchema.lean` (4 PURE).
- Instance (Ricci, pre-existing): `lean/E213/Lib/Math/Geometry/GeometrizationConjecture/RicciFlowDiscrete.lean`.
- ∅-axiom status: 0 DIRTY across all of the above.

## Narrative

### The generator

The schema's data is a step relation `R : X → X → Prop`, a monovariant
`μ : X → Nat`, and a normal-form predicate `NF : X → Prop`, subject to one
obligation:

> **`step : ∀ x, NF x ∨ ∃ y, R x y ∧ μ y < μ x`** — at every `x`, either `x` is a
> normal form, or there is an `R`-successor with strictly smaller `μ`.

`descent_reaches` then concludes `∃ y, NF y ∧ Reaches R x y` (a normal form is
reached, `Reaches` being the reflexive–transitive closure of `R`).  The proof is
`descent_reaches_fueled`: structural recursion on a `Nat` fuel bounding `μ x`,
eliminating the `Or`/`Exists` data *constructively* — no `Classical`, no decidable
equality on `X`.  This is exactly the well-founded-descent dual of A2 LOOP's
forward induction.

`descent_invariant` adds an invariant `I : X → α` preserved by every step
(`inv : ∀ x y, R x y → I x = I y`) and concludes the reached normal form carries
it: `I y = I x` (via `reaches_invariant`, induction on `Reaches`).  **The answer
is the invariant the descent preserves.**

`flow_reaches_of_relation` proves the original self-map archetype `flow_reaches`
*from* the relation schema (the graph relation `fun a b => f a = b`, normal form
`f x = x`, via `reaches_graph_iter`).  So A6 FLOW is literally subsumed — the
self-map form is the special case where `R` is a function's graph.

### One `propext` boundary

`descent_invariant`'s `I y = I x` is an *equality* in `α`.  When the natural
invariant is a **`Prop`** (e.g. `markovEq`, pairwise-coprimality), `I y = I x`
would be equality of `Prop`s — which needs `propext`, forbidden here.  The clean
move is to carry such an invariant in the **carrier** (a structure field), not as
`I`: then `descent_reaches` (no `I`) suffices and the answer reads off the normal
form.  UFD takes exactly this route; only `Nat`/data-valued invariants (gcd) ride
`descent_invariant` directly.

### The four instances

| Instance | Carrier | Step `R` | `μ ↓` | Normal form reads off |
|---|---|---|---|---|
| **GCD** | `Nat × Nat` | `(a,b) ↦ (b%a, a)` | `fst` | `gcd` (invariant via `descent_invariant`) |
| **UFD separation** | valuation-equal `(m,n)` | peel a shared prime | `m+n` | `m = n` |
| **Markov** | ordered triple | Vieta-jump ∘ re-sort | `max` | root `(1,1,1)` |
| **Ricci (discrete)** | curvature state | `spreadFlow` | curvature spread | constant curvature |

- **GCD** (`euclid_via_descent_invariant`): the reached normal form carries
  `gcd213` — the invariant-carrying schema reproduces the canonical result.
- **UFD separation** (`vp_separation_via_schema`): a pair with equal prime
  valuations everywhere peels shared primes to `(1,1)`; equality lifts back up the
  `Reaches` chain (`reaches_eq_back`, each peel having multiplied both coordinates
  by the same prime).  This is `vp_separation` (unique factorization) reproved
  through the schema.
- **Markov** (`markov_descends_to_root`): the first genuinely **relational**
  (non-self-map) instance.  The step is *nondeterministic* — the Vieta jump
  `c ↦ 3ab−c` is followed by a re-sort whose branch depends on where the jumped
  value lands — so `Down` is a relation, not a function.  Because `μ = max` is
  **permutation-invariant**, the re-sort folds into the bundled step while `μ`
  still strictly descends (`markov_mid_lt_max`); the schema absorbs the
  permutation with no quotient-by-symmetry.

The **shared generator** is `descent_reaches_fueled` (fuel-recursion on a
monovariant), one level *below* `iter` — it is well-founded descent, not forward
iteration, the FLOW side of the FLOW/LOOP duality.  This passes the
shared-generator criterion (`theory/meta/boundary_discipline.md`): not a shared
slogan but a shared proof-skeleton, verified across four independent files.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `descent_reaches` | `MonovariantFlow` | relation + descending monovariant ⟹ a normal form is reached |
| `descent_invariant` | `MonovariantFlow` | the reached normal form carries any step-invariant |
| `flow_reaches_of_relation` | `MonovariantFlow` | the self-map A6 archetype is the graph-relation special case |
| `vp_separation_via_schema` | `VpSeparationDescent` | UFD separation (`m=n` from equal valuations) as a descent instance |
| `markov_descends_to_root` | `MarkovDescentSchema` | every Markov triple descends to `(1,1,1)` — first relational instance |

## Research-note provenance

`research-notes/frontiers/descent_schema_universal.md` (Finding H, the corpus-wide
proof-shape sweep continuing `general_theory_metaanalysis.md`).

## Open frontier

- **Atomicity is a *degenerate* member, not promoted as a fifth instance.**
  `Theory/Atomicity/Five.atomic_implies_five` uses a single bounded Bézout shift as
  a *contradiction generator* (`μ = a` bounded `< 3`), not an iteration to a fixed
  point; it fits the schema's shape but not its spirit, so it is recorded as a
  boundary case, not inflated to "5 instances".  Clean unification = 4 iterated
  descents (GCD / UFD / Markov / Ricci).
- The smooth Ricci flow (Perelman entropy) remains the open geometric side
  (`research-notes/frontiers/ricci_flow_smooth_core.md`); only the discrete
  monovariant version is a schema instance.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Foundations.MonovariantFlow \
  E213.Lib.Math.Foundations.VpSeparationDescent \
  E213.Lib.Math.NumberSystems.Real213.Markov.MarkovDescentSchema
python3 tools/scan_axioms.py E213.Lib.Math.Foundations.MonovariantFlow
python3 tools/scan_axioms.py E213.Lib.Math.Foundations.VpSeparationDescent
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Real213.Markov.MarkovDescentSchema
```
