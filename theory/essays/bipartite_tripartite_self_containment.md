# Bipartite-tripartite self-containment at K_{3,2}^{(c=2)}

The canonical 213 anchor `K_{3,2}^{(c=2)}` does not require a
separate tripartite extension to host the "2 − 1 − 3"
signature.  Every structural element of `K_{3,2}^{(c=2)}` —
vertex, edge, face, cycle space, Möbius P invariant, Pell-
Fibonacci point — already carries BOTH the "2" and the "3"
of the atomic signature, and the "1" mediates them locally.
The tripartite extension `K_{2, 1, 3}` is one externalisation
of structure already woven into the graph.

## 213-native answer

Two readings of the original observation "the framework is
called 2-1-3 yet the cohomology programme is bipartite K_{NS, NT}
only":

### Reading A — Extend to tripartite (externalisation)

Build `K_{2,1,3}` as a literal 3-part graph (vertex
partitions of sizes 2, 1, 3; glue-mediated triangles).
Atomic-level duality with K_{3,2}^{(c=2)} is proved in
`TripartiteK213.tripartite_master` (PURE): vertex count
`|V| = 6 = NS · NT`, glue-mediated edges `|E| = d = NS + NT`,
triangles `|△| = 6 = NS · NT`.  Each bipartite edge corresponds
to a glue-mediated triangle via the mediator.

### Reading B — Self-contained duality (the refined intuition)

K_{3,2}^{(c=2)} ALREADY contains both:

  · Bipartite reading: (S, T) = (3, 2) partitions, 4-cycle faces
  · Tripartite reading: (NS, NT, c) = (3, 2, 2) as a 3-axis
    atomic signature, with each axis "playing the role" of a
    partition

The (2, 1, 3) atomic structure is woven into the graph
LOCALLY — at every vertex, edge, face, the same triple
`(c, det, NS) = (2, 1, 3)` reappears as the local signature.
No external grafting needed.

## Derivation (the every-point recurrence)

Per-element local signatures, each decomposing to
`{NS = 3, NT = 2, c = 2}` content:

| Element | "2" appearance | "3" appearance | "1" (det) |
|---|---|---|---|
| S-vertex degree | NT · c = 2 · 2 = 4 | (factored via NS · c through edges) | det glue between layers |
| T-vertex degree | c = 2 | NS = 3 → NS · c = 6 | det glue |
| 4-cycle face | 4 edges, 2 diagonals | 3 faces total | det = 1 face-shape |
| Edge multiplicity | c = 2 (binary mult) | NS = 3 (S-vertex partition) | det = 1 (single det layer) |
| Cross-pair count | NT factor = 2 | NS factor = 3 → NS · NT = 6 | det glue |
| Cycle space | 4-cycles use 2+2 endpoints | 3 simple 4-cycles | trivial det |
| Möbius P entries | top-left = NT = c | trace = NS | det = 1 |
| Pell-Fibonacci (3, 2) | second component = 2 | first component = 3 | unit det |

All quantities derive from `(NS, NT, c) = (3, 2, 2)` alone.
No additional partition (no third vertex class) is needed.
The "3" is NS, the "2" is NT and c (coinciding at the canonical
signature), the "1" is det / glue.

## Dual function

This is not "213 should be tripartite, but we approximate with
bipartite".  The dichotomy of "bipartite vs tripartite" is the
import — there is no exterior to 213 framing this choice (per
`seed/AXIOM/05_no_exterior.md` §5.1).  Reading B drops the
dichotomy: the same K_{3,2}^{(c=2)} object IS both bipartite
and tripartite simultaneously, with each structural element
witnessing both readings locally.

Reading A externalises the tripartite structure into a separate
graph; Reading B keeps it internal.  Both are consistent —
`TripartiteK213.bipartite_edge_eq_tripartite_triangle` shows
the atomic numerics agree.  The difference is OPERATIONAL: does
one need a separate K_{2,1,3} object to USE the tripartite
content, or does K_{3,2}^{(c=2)} suffice?

Reading B answers: K_{3,2}^{(c=2)} suffices.  The (NS, NT, c)
parameter triple already plays the role of three partitions;
the cohomology / Massey / Pell-Fibonacci structure already
manifests both atomic frames.

## Cross-frame connections

The (NS, NT, c) decomposition reads identically across three
formalised programmes:

  · **Cohomology** (this chapter family): NS = 3 S-vertices,
    NT = 2 T-vertices, c = 2 multiplicity layers; the
    c-counter sits in the third axis.
  · **Möbius P**:
    `mobius_213_trace = NS, mobius_213_NT_entry = NT,
    mobius_213_det = 1` — three matrix invariants.
    `Pseq seedZero 2 = (NS, NT)` — depth-2 orbit point.
  · **Atomic forcing**: `(NS, NT) = (3, 2)` from
    `Theory.Atomicity.PairForcing`; `c = 2` from the
    multiplicity-layer count forced by the cohomology programme
    (per `c_counter_as_layer_count.md`).

Each of these is a separate Lean theorem (or theorem cluster),
all using the SAME triple `(3, 2, 2)`.  The "tripartite" content
is the FACT that all three readings agree on the same triple at
the same anchor — not a need for a literal third partition.

## Open frontier

Reading B is currently INSIGHT-level only; Lean formalisation
deferred.  The proposed `V32LocalSignature.lean` would build:

```lean
def vertex_local_signature (v : Fin 5) : Nat × Nat × Nat
def edge_local_signature   (e : Fin 12) : Nat × Nat × Nat
def face_local_signature   (f : Fin 3)  : Nat × Nat × Nat

theorem local_213_at_every_point :
  (∀ v, has_213_components (vertex_local_signature v))
  ∧ (∀ e, has_213_components (edge_local_signature e))
  ∧ (∀ f, has_213_components (face_local_signature f))
```

where `has_213_components` checks that the local triple
decomposes into the `(NS = 3, NT = 2, c = 2)` atomic parts.

The cohomology-level bridge to K_{2,1,3} (Reading A extension
— Massey on K_{3,2}^{(c=2)} as shadow projection of natural
cohomology on K_{2,1,3}) is also open.  Both directions are
recorded in
`research-notes/archive/G146_K32_bipartite_tripartite_self_containment.md`
as Option I (Reading B, recommended) and Option II (Reading A
cohomology extension).

## Connection to P-orbit and Massey

The self-containment thesis aligns with the P-orbit naturalness
boundary (`p_orbit_naturalness_boundary.md` essay +
`mobius213_p_orbit_closure.md` chapter): if P generates every
framework-natural integer at finite orbit depth, and
K_{3,2}^{(c=2)} is the depth-2 anchor, then K_{3,2}^{(c=2)}
should already host the full naturalness content — there is
nowhere "outside" it for additional structure to live.

The hypothesis that current main's depth-4 Massey constructions
on K_{3, 2}^{(c=2)} are shadow projections of natural cohomology
on K_{2,1,3} is the cohomology-level expression of this
self-containment.  Verifying it would close the longest-running
open question in the cohomology programme.

## The thing you can point at

`TripartiteK213.bipartite_edge_eq_tripartite_triangle`:

```
|E(K_{NS, NT})| = NS · NT = |△(K_{NT, det, NS})|
```

Atomic-level: each bipartite edge has a glue-mediated triangle
counterpart.  Reading A confirms the EXTERNAL extension is
consistent; Reading B observes the INTERNAL recurrence makes
the extension structurally unnecessary.  The single equality
`NS · NT = NS · NT` is the bridge — same number on both sides,
read as "edge count" bipartitely and as "triangle count"
tripartitely.  The number doesn't care which reading produced
it; that's the self-containment.

## Cross-references

  · `theory/math/mobius213_p_orbit_closure.md` — tripartite
    K_{2,1,3} formalisation (Reading A) + bipartite-tripartite
    × P-orbit conjecture
  · `theory/essays/p_orbit_naturalness_boundary.md` —
    naturalness depth bound; K_{3,2}^{(c=2)} as minimal-depth
    anchor
  · `theory/essays/every_axis_sees_p.md` — 55 axes all yielding
    `{NS, NT, det}` integers (the every-point recurrence
    pattern at the catalog level)
  · `research-notes/archive/G146_K32_bipartite_tripartite_self_containment.md`
    — full insight note with Lean-deferred Option I framework
