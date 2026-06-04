# Tripartite K_{2, 1, 3} cohomology + K_{3, 2}^{(c=2)} self-containment

Two Lean sub-trees that jointly locate where the "3" of the
(2, 1, 3) atomic signature lives cohomologically.  The external
tripartite reading (K_{2, 1, 3} with rainbow-triangle 2-cells
filled) is cohomologically trivial above H⁰, so it cannot host
the (2, 1, 3) signature's H¹ richness.  The internal
self-containment reading (K_{3, 2}^{(c=2)} carries (2, 1, 3) as
local signature at every vertex / edge / face) is the only
cohomology-level path.

Companion to `bipartite.md` (K_{3, 2}^{(c=2)} 2-skeleton +
V32Betti) and `mobius213_p_orbit_closure.md` (tripartite
K_{2, 1, 3} atomic-count duality).  This chapter formalises
the cohomology-level verdict.

## Two graphs, two readings

| Graph | |V| | |E| | |△| | b₀ | b₁ | b₂ |
|---|---|---|---|---|---|---|
| K_{3, 2}^{(c=2)} | 5 | 12 | 0 | 1 | 8 | 0 |
| K_{2, 1, 3} (+ △ 2-cells) | 6 | 11 | 6 | 1 | 0 | 0 |

K_{3, 2}^{(c=2)}'s `b₁ = NS² − 1 = 8` is the photon-kernel
dimension (`V32Betti.b1_eq_NS_sq_minus_1`).  K_{2, 1, 3}'s
`b₁ = 0`: every cycle = sum of triangle boundaries
(`V213Betti.K213_betti_capstone`).

The bipartite-tripartite atomic-level duality holds:
`|E(K_{3, 2})| = NS · NT = 6 = NT · det · NS = |△(K_{2, 1, 3})|`.
Each bipartite edge lifts to a glue-mediated triangle
(`Mobius213/Px/TripartiteK213.bipartite_edge_eq_tripartite_triangle`).
But this is a count-level match, not a cohomology-level
isomorphism.

## K_{2, 1, 3} cohomology

The complete tripartite K_{NT, det, NS} = K_{2, 1, 3} has:

  · 6 vertices (NT = 2 + det = 1 + NS = 3)
  · 11 edges (NT·det + det·NS + NT·NS = 2 + 3 + 6 — the
    glue-mediated 5 + the 6 direct NS-NT edges)
  · 6 rainbow triangles (one per (NT-vertex, det-vertex,
    NS-vertex) triple)

Cochain spaces: `|C⁰| = 2⁶ = 64`, `|C¹| = 2¹¹ = 2048`,
`|C²| = 2⁶ = 64`.

The key structural fact (`V213Betti.delta1_pivot_lift_pointwise`,
PURE): each direct edge `c_{ij}` (positions 5..10) appears in
**exactly one** triangle.  So the singleton indicator of
`faceEdge3 f` is a δ¹-preimage of the singleton indicator of
triangle f.  δ¹ is surjective constructively, with the
direct-edge `c_{ij}` as pivot.

Numerical signature (`V213Betti.betti_numerics`, PURE):

  · `|ker δ⁰| = 2` ⇒ `b₀ = 1` (connected, decide-verified
    over 64 cochains)
  · `|im δ⁰| = 64 / 2 = 32`
  · `|im δ¹| = |C²| = 64` (surjective) ⇒ `b₂ = 0`
  · `|ker δ¹| = 2048 / 64 = 32`
  · `b₁ = dim ker δ¹ − dim im δ⁰ = 5 − 5 = 0`

Euler χ = |V| − |E| + |F| = 6 − 11 + 6 = 1, matching
`b₀ − b₁ + b₂ = 1`.

Capstone: `K213_betti_capstone` (7-conjunct PURE) bundles
b₀ via kernel size, δ¹ surjectivity lift, and the numerical
identities.

## K_{3, 2}^{(c=2)} local (2, 1, 3) signature

`V32LocalSignature.lean` (15 PURE) gives the positive reading:
the (2, 1, 3) atomic multiset reappears at every structural
locus of K_{3, 2}^{(c=2)} without external partition.

### Predicate

```
is_213_multiset a b c := (a + b + c == 6) && (a · b · c == 6)
```

For three positive naturals, sum 6 and product 6 force
multiset {1, 2, 3} uniquely.  Both `(NT, 1, NS) = (2, 1, 3)`
and `(NS, 1, NT) = (3, 1, 2)` decide-verify as 213-multiset
(`canonical_213`, `canonical_213_swapped`).

### Local signatures

  · **Vertex** (Fin 5): S-side `(NT, det, NS) = (2, 1, 3)`;
    T-side `(NS, det, NT) = (3, 1, 2)` — same multiset, axes
    swapped (`S_vertex_signature_components`,
    `T_vertex_signature_components`).
  · **Edge** (Fin 12): uniform `(NT, det, NS) = (2, 1, 3)`
    (`edge_signature_uniform`).
  · **Face** (Fin 3, simple 4-cycles): uniform
    `(NT, det, NS) = (2, 1, 3)` (`face_signature_uniform`).

All three checked via `decide` over the finite vertex / edge /
face index sets (`vertex_signature_is_213`,
`edge_signature_is_213`, `face_signature_is_213`).

### Master capstone

`local_213_at_every_point` (5-conjunct PURE):

```
(∀ v : Fin 5,  sig_213 (vertex_local_signature v) = true)
∧ (∀ e : Fin 12, sig_213 (edge_local_signature e) = true)
∧ (∀ f : Fin 3,  sig_213 (face_local_signature f) = true)
∧ is_213_multiset NT 1 NS = true
∧ is_213_multiset NS 1 NT = true
```

The "3" of the (2, 1, 3) signature reproduces locally at
every datum.  No external partition needed.

## Cross-frame verdict

`V32V213CohomologyBridge.lean` (3 PURE) bundles the structural
comparison:

  · `atomic_bridge` (3-conjunct PURE):
    bipartite `NS · NT = 6`, tripartite `NT · det · NS = 6`,
    they are equal — atomic-level duality preserved.
  · `b1_mismatch` (2-conjunct PURE):
    bipartite `b₁ = NS² − 1 = 8`, tripartite `b₁ = 0` —
    cohomology-level duality broken.
  · `self_containment_cohomology_verdict` (6-conjunct PURE
    master): atomic preservation + cohomology breach +
    structural sources (`V32Betti.b1_eq_NS_sq_minus_1` on the
    bipartite side, `V213Betti.delta1_pivot_lift_pointwise` on
    the tripartite side).

The structural conclusion: the K_{2, 1, 3} triangle-filling
kills all 1-cycles (cycle space dim equals triangle count, so
every cycle bounds).  K_{3, 2}^{(c=2)} has cycle-space dim 8
with no filled 2-cells in the bare graph, leaving all 8 cycles
unbounded.  The external tripartite reading cannot host the
cohomological "3" of K_{3, 2}^{(c=2)}.

The internal self-containment reading (V32LocalSignature) is
the only cohomology-level path consistent with the (2, 1, 3)
atomic content.

## Lean source

  · Umbrella: `lean/E213/Lib/Math/Cohomology/Tripartite.lean`
  · Tripartite cohomology:
    - `Tripartite/V213.lean` — CochV / CochE / CochF + δ⁰ /
      δ¹ + edge endpoints + triangle face edges
    - `Tripartite/V213Betti.lean` — Betti capstone via δ⁰
      kernel enumeration + δ¹ pivot lift
    - `Tripartite/V32V213CohomologyBridge.lean` — cross-frame
      verdict (atomic preserved / cohomology broken)
  · K_{3, 2}^{(c=2)} self-containment:
    - `Bipartite/V32LocalSignature.lean` — local-(2, 1, 3)
      framework + master capstone

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `K213_betti_capstone` | `Tripartite.V213Betti` | (b₀, b₁, b₂) of K_{2, 1, 3} = (1, 0, 0) |
| `delta1_pivot_lift_pointwise` | same | each triangle indicator is δ¹ of unique direct-edge indicator |
| `kerSizeDelta0_eq_2` | same | b₀ = 1 (connected, 64-cochain enumeration) |
| `local_213_at_every_point` | `Bipartite.V32LocalSignature` | (2, 1, 3) multiset at every vertex / edge / face |
| `canonical_213` | same | `is_213_multiset NT 1 NS = true` |
| `S_vertex_signature_components` / `T_vertex_signature_components` | same | side-split vertex signature reading |
| `atomic_bridge` | `V32V213CohomologyBridge` | `|E(K_{3,2})| = 6 = |△(K_{2,1,3})|` |
| `b1_mismatch` | same | `b₁ = 8` (bipartite) vs `b₁ = 0` (tripartite) |
| `self_containment_cohomology_verdict` | same | atomic preserved + cohomology broken (master) |

## Research-note provenance

    — original insight + Option I / II proposal; both now
    closed with the verdict above

## Open frontier

  · **Cup-product transport on V32LocalSignature**: extend
    `local_213_at_every_point` to the cup ring — does the
    (2, 1, 3) local signature persist under cup products
    `H^k × H^l → H^(k+l)` at K_{3, 2}^{(c=2)}?
  · **Local Massey transport**: do the depth-4 Massey
    constructions on K_{3, 2}^{(c=2)} (`MasseyFourFoldH1`,
    `V33Massey4Fold` family) factor through the local
    (2, 1, 3) signature?  Conjecturally yes; explicit map
    is open.
  · **Local-signature generalisation**: does
    `K_{NS, NT}^{(c)}` carry an analogous local
    `(NT, det, NS)`-multiset signature for general (NS, NT)?
    Trivially yes by structure transport; cohomology-level
    consequences less clear.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Cohomology.Tripartite
cd lean && lake build E213.Lib.Math.Cohomology.Bipartite.V32LocalSignature
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Tripartite.V213Betti
python3 tools/scan_axioms.py \
  E213.Lib.Math.Cohomology.Tripartite.V32V213CohomologyBridge
python3 tools/scan_axioms.py \
  E213.Lib.Math.Cohomology.Bipartite.V32LocalSignature
```

## Cross-references

  · `theory/math/cohomology/bipartite.md` — V32Betti, parametric
    Euler / b_1 family (K_{3, 2}^{(c=2)} parent overview)
  · `theory/math/cohomology/k_nm_c_classification.md` —
    K_{NS, NT}^{(c)} 3-axis classification
  · `theory/math/algebra/mobius213_p_orbit_closure.md` — tripartite
    K_{2, 1, 3} atomic-level duality (count side)
  · `theory/essays/p_orbit/bipartite_tripartite_self_containment.md` —
    cross-cutting essay (insight + verdict synthesis)
  · `theory/essays/p_orbit/every_axis_sees_p.md` — 55 framework axes,
    all yielding `{NS, NT, det}` (the every-point recurrence
    pattern at the catalog level)
