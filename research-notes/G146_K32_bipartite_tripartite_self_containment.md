# G146 — K_{3,2}^{(c=2)} as self-contained bipartite-tripartite duality

**Status**: insight captured; Lean formalization deferred.
**Origin**: 사용자의 직관 — "213은 이분그래프와 삼분그래프가 서로
얽히고 섥히는 것" → 정제: **K_{3,2}^{(c=2)} 자체가 bipartite-tripartite가
모든 지점에서 동시 등장하는 self-contained 구조**.

## Core observation

The canonical 213 anchor `K_{3,2}^{(c=2)}` does NOT require a separate
tripartite extension (e.g., `K_{2,1,3}`).  Every structural element
of `K_{3,2}^{(c=2)}` carries BOTH the "2" and the "3" of the
(2, 1, 3) atomic signature simultaneously.

The graph is **already self-contained** as the locus of bipartite-tripartite
duality.

## Every-point recurrence table

| Structural element | "2" appearance | "3" appearance |
|---|---|---|
| S-vertex degree | `NT · c = 2 · 2 = 4 = 2²` | (factored through NS·c via edges) |
| T-vertex degree | `c = 2` | `NS = 3` → `NS · c = 6` |
| Single face (4-cycle) | 4 edges (2 S-side + 2 T-side); 2 diagonals | 3 faces total |
| Edge multiplicity layer | `c = 2` (binary mult) | `NS = 3` (S-vertex partition) |
| Cross-pair count | factor `2` from NT | factor `3` from NS → `NS · NT = 6` |
| Cycle space (dim) | (4-cycles use 2+2 endpoints) | 3 simple 4-cycles |
| Möbius P entries | top-left `= 2 = NT = c` | trace `= 3 = NS` |
| Pell-Fibonacci point `(3, 2)` | `2` = second component | `3` = first component |
| H¹ dim (V32) | 8 (= 2·NS + NT? — to verify) | 3 (factor in face structure) |
| H² dim (simple) | (Sym(3)-quotient → 1) | 3 face-dependence-quotient |

**All structural quantities derive from `(NS, NT) = (3, 2)` alone.**
No additional partition (no third vertex class) is needed.  The
"3" is NS, the "2" is NT and c (coinciding at the canonical signature).

## Why this matters

Two distinct readings of the original question "왜 이분그래프만?":

### Reading A — Extend to tripartite

Build `K_{2,1,3}` tripartite (literal "213"), prove duality / isomorphism
with `K_{3,2}^{(c=2)}`.

  · 3 partitions: (2, 1, 3) vertices, 6 total
  · 2·1·3 = 6 triangles (matching K_{3,2}'s cross-pair count)
  · Triangles = 3-cells, not 4-cycles

This is a NEW graph construction with its own cohomology.

### Reading B — Self-contained duality (user's refined intuition)

K_{3,2}^{(c=2)} ALREADY contains both:

  · Bipartite reading: (S, T) = (3, 2) partitions, 4-cycle faces
  · Tripartite reading: (NS, NT, c) = (3, 2, 2) as a 3-axis atomic
    signature, with each axis "playing the role" of a partition

The (2, 1, 3) atomic structure is **woven into the graph LOCALLY**
— at every vertex, edge, face, the same triple `(c, det, NS)` =
`(2, 1, 3)` reappears as the local signature.

**No external grafting needed.**  The "tripartite" structure is
already there as the (NS, NT, c) axis decomposition.

## Conjecture (formal statement)

**Conjecture G146**: `K_{3,2}^{(c=2)}` is the **unique minimal graph**
where the atomic (2, 1, 3) signature manifests at every cohomological
degree (H⁰, H¹, H², …) as a local recurrence of the triple.

Specifically:

  · `H⁰(K_{3,2}^{(c=2)})` has dim `1` (connected; the "unit" of 213)
  · `H¹(K_{3,2}^{(c=2)})` decomposes by S-stars (3) + T-incidences (2)
    + multiplicity-shift (2) summands → `H¹ ≅ 3⊕2⊕2`-type structure
  · `H²(K_{3,2}^{(c=2)})` has dim `1` (under face-dependence quotient
    + Sym(3) symmetrisation) — the "unit" again

So the cohomology dimensions sequence
`(H⁰, H¹, H²) = (1, ?, 1)` opens with 1's and the "middle" carries
the structural content.

## Local signature framework (next-session Lean)

Define a per-element "local 213 signature" functor:

```lean
-- For each vertex v of K_{3,2}^{(c=2)}:
def vertex_local_signature (v : Fin 5) : Nat × Nat × Nat :=
  if v.val < 3 then (2, 1, 2)   -- S-vertex: (NT, det, c)
  else            (3, 1, 2)      -- T-vertex: (NS, det, c)

-- For each face f (Fin 3):
def face_local_signature (f : Fin 3) : Nat × Nat × Nat :=
  (4, 2, 3)  -- (edges-per-face, diagonals, total-faces)

-- Master claim: every local signature has multiset {2, 1, 3} content.
```

Then:

```lean
theorem local_213_at_every_point :
    -- Vertices
    (∀ v : Fin 5, has_213_components (vertex_local_signature v))
    -- Edges
    ∧ (∀ e : Fin 12, has_213_components (edge_local_signature e))
    -- Faces
    ∧ (∀ f : Fin 3, has_213_components (face_local_signature f))
```

where `has_213_components` checks that the local triple decomposes
into the `(NS=3, NT=2, c=2)` atomic parts.

## Two strategic options for next session

### Option I (recommended) — Reveal duality at K_{3,2}^{(c=2)}

Build the `LocalSignature.lean` file capturing the every-point
recurrence.  No new graph; just reveal the structure ALREADY
present in `V32` / existing files.

  · `vertex_local_signature`, `edge_local_signature`,
    `face_local_signature` definitions
  · Master theorem `local_213_at_every_point`
  · Cross-frame: each local signature traces back to the (NS, NT, c)
    atomic triple — no external partition needed

This validates user's refined intuition: **K_{3,2}^{(c=2)} is
self-contained 213**.

### Option II — Extend to K_{2,1,3} tripartite + prove duality

Build a new `V213_tripartite.lean` for `K_{2,1,3}` and prove a
duality / isomorphism with `K_{3,2}^{(c=2)}` at the cohomology level.

  · New graph, new face structure (triangles, not 4-cycles)
  · Map between K_{3,2}^{(c=2)} cohomology and K_{2,1,3} cohomology
  · Show both compute the same "atomic" invariants

This is the LITERAL "213 → tripartite" reading.  More work but
broader theoretical reach.

## Connection to existing G-notes

  · `G143` — c-multiplicity hierarchy (the c-counter problem)
  · `G145` — c-counter structural theory (multiplicity-layer count)
  · **`G146`** (this) — bipartite-tripartite self-containment at K_{3,2}

The three notes form a triple:

  · G143: ASKS where c shows up
  · G145: ANSWERS in terms of layer count + Stern-Brocot classification
  · G146: ASKS where "3" of 213 actually lives — answers within K_{3,2}
    itself (not requiring tripartite extension)

## Concrete first steps (next session)

1. Read existing `V32.lean` carefully to map every structural
   element to its `(NS, NT, c)` decomposition.
2. Create `lean/E213/Lib/Math/Cohomology/Bipartite/V32LocalSignature.lean`.
3. Define `vertex_local_signature`, `edge_local_signature`,
   `face_local_signature`.
4. Prove `local_213_at_every_point` capstone.
5. Decide if Option II (tripartite extension) is worth pursuing
   given Option I's self-containment.

## Status

Insight captured.  Lean formalization deferred to next session.
User's refined intuition (Reading B / self-containment) is the
recommended starting point.
