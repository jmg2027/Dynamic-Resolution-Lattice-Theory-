# Mediant cohomology functor

The Stern-Brocot mediant
`(NS₁, NT₁) ⊕ (NS₂, NT₂) = (NS₁+NS₂, NT₁+NT₂)` on bipartite
multigraph indices lifts to a **Vandermonde decomposition** of
every K_{NS, NT}^{(c)} cell count.  Vertex counts split
linearly, edge counts into four bipartite cells, and face
counts into nine factored-Vandermonde² products.  The
assignment `(NS, NT) ↦ (V, E, F)` is a functor over the
Stern-Brocot poset.

Companion to `k_nm_c_classification.md` (universal
`(NS, NT, c)` cohomology) and
`bipartite.md` (K_{3, 2}^{(c=2)} Betti numbers).  Both sides of
the mediant ⊕ here are the count-Vandermonde face; the
cup-product / cochain lift is the open next layer.

## Combinatorial heart

`binom_add_2 : binom (a + b) 2 = binom a 2 + binom b 2 + a · b`
(`Lib/Math/Combinatorics/Binomial.lean`).  A 2-subset of `a + b`
lies entirely in the first `a` (count `binom a 2`), entirely in
the last `b` (`binom b 2`), or has one element on each side
(`a · b`).  This is the universal Pascal-level identity from
which the mediant decomposition descends.

## Three Vandermonde decompositions

`Cohomology/MediantCohomologyFunctor.lean` (22 PURE,
∅-axiom):

  · **Vertex** (linear additivity):
    `V(a+c, b+d) = V(a, b) + V(c, d)`
    (`vertexCount_mediant`).  Direct from regrouping a sum of
    four Nats.
  · **Edge** (4-term Vandermonde):
    `E^m(a+c, b+d) = E^m(a, b) + E^m(a, d) + E^m(c, b) +
    E^m(c, d)` (`edgeCount_mediant`).  The four edge classes
    are intra-1 (`K_{a, b}` edges), cross-12 (`K_{a, d}`),
    cross-21 (`K_{c, b}`), intra-2 (`K_{c, d}`).
  · **Face** (factored Vandermonde²):
    `F(a+c, b+d) = (binom a 2 + binom c 2 + a · c)
                 · (binom b 2 + binom d 2 + b · d)`
    (`faceCount_mediant_factored`).  9 products total, one per
    (S-pair source × T-pair source) combination.

The edge proof uses `add_mul_pure` — the propext-free right
distribution `(a + b) · c = a · c + b · c`, re-derived in
`Combinatorics/Binomial.lean` to avoid `propext` in
`Nat.right_distrib`.

## K_{4, 3} = K_{1, 1} ⊕ K_{3, 2} marquee

The Stern-Brocot relation
`(4, 3) = (1, 1) ⊕ (3, 2)` is the first non-trivial mediant
position (K_{4, 3} interior to the Stern-Brocot tree, between
the seedZero and seedInf thin chains).  At c = 2:

  · `7  = 2 + 5` (vertex additivity)
  · `24 = 2 + 4 + 6 + 12` (edge 4-term)
  · `18 = (0 + 3 + 3) · (0 + 1 + 2) = 6 · 3 = 18`
    (face factored Vandermonde²; 4 of 9 terms non-zero,
    `binom 1 2 = 0` zeroing the other 5)

`K43_{vertex,edge,face}_from_mediant`,
`K43_face_9term_evaluation` decide-verify each line.

Cross-link: matches `V43.K43_{vertex,edge,simple_face}_count`
exactly.

## The functor

A `CountTriple` packages `(V, E, F)`.  The mediant lifts to a
**Vandermonde algebra law on counts**: V-component binary
additive, E-component 4-term Vandermonde, F-component factored
Vandermonde² (`countTriple_mediant_decomposition`).

Since every coprime `(NS, NT) ≥ (1, 0)` is Stern-Brocot
reachable (`Mobius213SternBrocot.reachable_of_pos`), every
`K_{NS, NT}^{(c)}` cell count is computable as a finite sum of
products of `binom` values along the unique Stern-Brocot path
from seeds `(0, 1), (1, 0)` to `(NS, NT)`.  This is the
functorial closure of "Stern-Brocot classifies bipartite
multigraphs": classifies = factors counts through.

## Master capstone

`mediant_cohomology_functor_capstone` (7-conjunct PURE):
Vandermonde-2 universal identity + V/E/F decompositions +
K_{4, 3} concrete + Stern-Brocot reachability of (4, 3).

## Lean source

  · Umbrella:
    `lean/E213/Lib/Math/Cohomology/MediantCohomologyFunctor.lean`
  · Combinatorial heart:
    `lean/E213/Lib/Math/Combinatorics/Binomial.lean`
    (`binom_n_0`, `binom_n_1`, `binom_succ_2`, `binom_add_2`,
    `add_mul_pure`)
  · Stern-Brocot reachability:
    `lean/E213/Lib/Math/NumberSystems/Real213/Mobius/Mobius213SternBrocot.lean`
  · Cell-count check:
    `lean/E213/Lib/Math/Cohomology/Bipartite/V43.lean`
    (K_{4, 3} counts)
  · ∅-axiom PURE on production critical path

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `binom_add_2` | `Combinatorics.Binomial` | Vandermonde-2: `binom (a+b) 2 = binom a 2 + binom b 2 + a·b` |
| `add_mul_pure` | same | propext-free right distribution `(a+b)·c = a·c + b·c` |
| `vertexCount_mediant` | `MediantCohomologyFunctor` | V mediant 2-term |
| `edgeCount_mediant` | same | E mediant 4-term Vandermonde |
| `faceCount_mediant_factored` | same | F mediant factored Vandermonde² |
| `countTriple_mediant_decomposition` | same | (V, E, F) joint mediant algebra |
| `K43_face_9term_evaluation` | same | 9-term face expansion at K_{4, 3} |
| `mediant_cohomology_functor_capstone` | same | 7-conjunct master |

## Open frontier

  · **Cochain-level lift**: identify the 4 edge classes and 9
    face classes as concrete sub-cochain sub-spaces of
    `K_{a+c, b+d}^{(c)}` cochains.  Define a cup-product
    extension respecting the mediant decomposition.
  · **Massey-class lift**: do 4-fold Massey witnesses on
    K_{4, 3} factor through K_{1, 1} ⊕ K_{3, 2}?  Cross-frame
    statement; depth-4 Massey on K_{3, 2} is the anchor
    (`V33Massey4Fold`).
  · **Counter-direction**: does the Vandermonde structure
    DETERMINE the cup-product algebra of K_{NS, NT}^{(c)}?
    If yes, K_{NS, NT}^{(c)} cohomology is reconstructible from
    K_{0, 1}^{(c)} and K_{1, 0}^{(c)} via Stern-Brocot mediant
    + Vandermonde lift.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Cohomology.MediantCohomologyFunctor
python3 tools/scan_axioms.py \
  E213.Lib.Math.Cohomology.MediantCohomologyFunctor
python3 tools/scan_axioms.py E213.Lib.Math.Combinatorics.Binomial
```

## Cross-references

  · `theory/math/cohomology/k_nm_c_classification.md` —
    universal `(NS, NT, c)` cohomology classification
  · `theory/math/algebra/mobius_canonical_equivalence.md` — Möbius P,
    Stern-Brocot mediant closure
  · `theory/essays/cohomology/vandermonde_mediant_counts.md` —
    cross-cutting essay on the count-Vandermonde structure
  · `theory/essays/p_orbit/stern_brocot_as_universal_lattice.md` —
    Stern-Brocot tree as universal sample space
