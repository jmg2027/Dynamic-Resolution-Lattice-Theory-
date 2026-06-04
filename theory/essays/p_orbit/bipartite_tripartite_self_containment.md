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

## Both readings now formalised — verdict

Reading B (self-containment, Option I) — **CLOSED positive**
in `V32LocalSignature.lean` (15 PURE).  The predicate
`is_213_multiset a b c := (a+b+c == 6) && (a·b·c == 6)`
uniquely characterises the multiset `{1, 2, 3}` for positive
naturals.  At every vertex, edge, face of K_{3,2}^{(c=2)}:

  · vertex (Fin 5): S-side `(NT, 1, NS) = (2, 1, 3)`;
    T-side `(NS, 1, NT) = (3, 1, 2)` — same multiset
  · edge (Fin 12): uniform `(NT, 1, NS) = (2, 1, 3)`
  · face (Fin 3): uniform `(NT, 1, NS) = (2, 1, 3)`

Master: `local_213_at_every_point` (5-conjunct decide-verified
capstone).  The "3" of the signature is reproduced locally at
every datum.

Reading A (external tripartite, Option II) — **CLOSED negative
at the cohomology level**, in
`Cohomology/Tripartite/V213Betti.lean` (13 PURE) +
`V32V213CohomologyBridge.lean` (3 PURE).  K_{2, 1, 3} with
the 6 rainbow triangles filled has Betti numbers
`(b₀, b₁, b₂) = (1, 0, 0)`.  The δ¹ surjectivity is
constructive: each triangle indicator is δ¹ of the unique
direct-edge indicator (`delta1_pivot_lift_pointwise`).

Atomic-level duality preserved:
`|E(K_{3,2})| = NS · NT = 6 = NT · det · NS = |△(K_{2,1,3})|`.

Cohomology-level duality FAILS:
`b₁(K_{3,2}^{(c=2)}) = 8 ≠ 0 = b₁(K_{2,1,3})`.

The K_{2,1,3} triangle-filling kills all 1-cycles structurally
(cycle space dim = triangle count, so every cycle bounds).
K_{3,2}^{(c=2)} has cycle-space dim `NS² − 1 = 8` with no
filled 2-cells in the bare graph reading, leaving all
8 cycles unbounded.  The external tripartite reading cannot
host the cohomological "3" of K_{3,2}^{(c=2)}.

The verdict
`self_containment_cohomology_verdict` (6-conjunct PURE)
bundles the atomic preservation + cohomology breach + structural
sources.  **Reading B is the cohomology-level path; Reading A
is a count-level coincidence only.**

## Connection to P-orbit and Massey

The self-containment thesis aligns with the P-orbit naturalness
boundary (`p_orbit_naturalness_boundary.md` essay +
`mobius213_p_orbit_closure.md` chapter): if P generates every
framework-natural integer at finite orbit depth, and
K_{3,2}^{(c=2)} is the depth-2 anchor, then K_{3,2}^{(c=2)}
should already host the full naturalness content — there is
nowhere "outside" it for additional structure to live.

The Massey-as-shadow-projection hypothesis (current main's
depth-4 Massey constructions on K_{3, 2}^{(c=2)} as shadow
projections of natural cohomology on K_{2,1,3}) is now
**REFUTED**.  `K_{2, 1, 3}` is cohomologically trivial above
H⁰ (`V213Betti.K213_betti_capstone`), so it can host no shadow
projection of the b₁ = 8 + Massey structure of K_{3, 2}^{(c=2)}.
The Massey content lives intrinsically in K_{3, 2}^{(c=2)}; no
external tripartite extension reaches it.

This is the structural negative that makes Reading B the only
viable cohomology-level reading.  The "3" of the (2, 1, 3)
signature must live within K_{3, 2}^{(c=2)} itself — and
`V32LocalSignature.local_213_at_every_point` proves it does,
constructively, at every datum.

## The thing you can point at

Two Lean theorems, one positive and one negative, jointly
locate the self-containment:

  · `V32LocalSignature.local_213_at_every_point` (PURE):
    every vertex, edge, face of K_{3, 2}^{(c=2)} has 213-multiset
    local signature — the "3" is internal.
  · `V32V213CohomologyBridge.self_containment_cohomology_verdict`
    (PURE): atomic-level duality `|E| = |△| = 6` preserved,
    cohomology-level duality `b₁ = 8 ≠ 0` broken — the external
    tripartite cannot host the cohomological "3".

The positive theorem says the "3" lives inside K_{3, 2}^{(c=2)};
the negative theorem says it does not live anywhere else.
Together they make self-containment a Lean-checked fact, not
just an insight: K_{3, 2}^{(c=2)} is the unique locus of the
(2, 1, 3) atomic signature at the cohomology level.

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
    — full insight note with Lean-deferred Option I framework
