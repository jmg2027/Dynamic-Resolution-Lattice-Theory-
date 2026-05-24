# Vandermonde counts under the Stern-Brocot mediant

Every cell count of `K_{NS, NT}^{(c)}` — vertices, edges,
faces — splits cleanly under the Stern-Brocot mediant
`(NS₁, NT₁) ⊕ (NS₂, NT₂) = (NS₁+NS₂, NT₁+NT₂)`.  The splits
are Vandermonde-style: 2-term for vertices, 4-term for edges,
9-term (factored Vandermonde²) for faces.  The combinatorial
heart is `binom (a + b) 2 = binom a 2 + binom b 2 + a · b`.

## 213-native answer

A graph mediant `K_{a, b} ⊕ K_{c, d} = K_{a+c, b+d}` is the
direct image of the Stern-Brocot mediant under the cell-count
functor.  Cell counts respect the mediant operation via three
Vandermonde identities (`MediantCohomologyFunctor.lean`,
22 PURE, ∅-axiom):

  · `V(a+c, b+d) = V(a, b) + V(c, d)` — vertex sets disjoint
    union.
  · `E^m(a+c, b+d) = E^m(a, b) + E^m(a, d) + E^m(c, b) + E^m(c, d)`
    — edges split by `(S-side, T-side) ∈ {a, c} × {b, d}`,
    four bipartite cells.
  · `F(a+c, b+d) = (binom a 2 + binom c 2 + a·c) ·
    (binom b 2 + binom d 2 + b·d)` — face cells = (S-pair
    source) × (T-pair source), with 3 × 3 = 9 (source pair)
    combinations.

Each face's S-pair-source is one of: intra-a, intra-c, or
cross-ac.  Each T-pair-source is one of: intra-b, intra-d,
or cross-bd.  The 9 products enumerate the face cells of
the merged graph.

## Derivation

The combinatorial heart is `binom_add_2`:

```
binom (a + b) 2 = binom a 2 + binom b 2 + a · b
```

Reading: a 2-subset of `a + b` lies entirely in the first
`a` (count: `binom a 2`), entirely in the last `b`
(`binom b 2`), or has one element on each side (`a · b`).

The vertex / edge / face decompositions all derive from this:

  · Vertex: the trivial split `(a + c) + (b + d) =
    (a + b) + (c + d)`.  Just regrouping.
  · Edge: `(a + c) · (b + d) = ab + ad + cb + cd`.  Bilinear
    expansion.  Each `·` is `binom n 1 · binom k 1 = n · k`,
    the count of (S, T) ordered pairs.
  · Face: apply `binom_add_2` to BOTH factors of
    `binom (a + c) 2 · binom (b + d) 2`.  Two 3-term factors
    multiply to 9 products.

The Lean proof uses `add_mul_pure` — a re-derivation of
`(a + b) · c = a · c + b · c` to avoid `propext` in
`Nat.right_distrib`.  Every identity holds at the level of
`decide`.

## Dual function

This is not "K_{NS, NT}^{(c)} cohomology IS a functor on
Stern-Brocot".  Count-level Vandermonde is closed; the
cochain-level lift (cup products, Massey classes) is open.
The reframing is operational: the *count algebra* of bipartite
multigraphs IS functorial under Stern-Brocot.  Anything that
factors through cell counts (Betti numbers via Euler χ,
combinatorial 4-cycle dependence counts, graph genus bounds)
inherits the Vandermonde structure for free.

The classical reading would derive K_{4,3}'s face count
`18 = 6 · 3` by direct computation (`binom 4 2 · binom 3 2`).
The Vandermonde reading derives it from K_{1,1} and K_{3,2}
via mediant — `18 = 0·0 + 0·1 + 0·(1·2) + 3·0 + 3·1 + 3·(1·2)
+ (1·3)·0 + (1·3)·1 + (1·3)·(1·2) = 0 + 0 + 0 + 0 + 3 + 6 +
0 + 3 + 6 = 18`.  Same number, different decomposition.  The
Vandermonde decomposition is structural; direct computation
collapses the structure into a single product.

## Cross-frame connections

Three readings of the Vandermonde identity:

  · **Combinatorial**: 2-subsets of `a + b` split by intra /
    cross.  Standard Pascal recursion at level 2.
  · **Algebraic**: `(x + y)² = x² + y² + 2·x·y`, restricted to
    `binom n 2 = n·(n-1)/2`.  The `a · b` cross term is
    half the `2·x·y` coefficient (since `binom n 2` already
    halves).
  · **Functorial**: count assignment `(NS, NT) ↦ binom NS 2 ·
    binom NT 2` factors through the Stern-Brocot mediant.
    Every mediant decomposition lifts to a Vandermonde
    decomposition of the count.

`MediantCohomologyFunctor` shows all three coincide on the
same Lean theorem.  The mediant-functor reading IS the
Vandermonde-identity reading IS the Pascal-Pascal-product
reading.

## Stern-Brocot terminus

Every Stern-Brocot reachable `(NS, NT) ≥ (1, 0)` has a unique
finite-depth mediant decomposition path from the two seeds
`(0, 1), (1, 0)` (`Mobius213SternBrocot.reachable_of_pos`).
Combined with the Vandermonde identities, every
`K_{NS, NT}^{(c)}` cell count is computable as a finite sum
of products of `binom` values along the path.

This is the operational closure of "Stern-Brocot classifies
bipartite multigraphs": classifies = factors counts through.
Direction E of the c-counter programme is closed at the count
level.

## Open frontier

  · **Cochain-level lift**: identify the 4 edge classes and
    9 face classes as concrete sub-cochain sub-spaces of
    `K_{a+c, b+d}^{(c)}` cochains.  Define a cup-product
    Mealy-like extension respecting the mediant decomposition.
  · **Massey-class lift**: 4-fold Massey witnesses on
    K_{4, 3} factor through K_{1, 1} and K_{3, 2}?
    Cross-frame statement; depth-4 Massey on K_{3, 2} is the
    anchor (`V33Massey4Fold`).
  · **Counter-direction**: does the Vandermonde structure
    DETERMINE the cup-product algebra of K_{NS, NT}^{(c)}?
    If yes, K_{NS, NT}^{(c)} cohomology is reconstructible
    from K_{0, 1}^{(c)} and K_{1, 0}^{(c)} via Stern-Brocot
    mediant + Vandermonde lift.

## The thing you can point at

`K43_face_factored_evaluation`:

```
(binom 1 2 + binom 3 2 + 1 * 3)
  * (binom 1 2 + binom 2 2 + 1 * 2) = 18
```

One Lean decide-verification.  K_{4, 3}'s 18 simple 4-cycle
faces decompose as `6 · 3 = (0 + 3 + 3) · (0 + 1 + 2)` via
the K_{1, 1} ⊕ K_{3, 2} mediant.  The factored Vandermonde²
is reading 18 as a 3-source × 3-source bilinear quantity,
not as a single product.  The structural content the direct
computation hides.

## Cross-references

  · `theory/math/cohomology/k_nm_c_classification.md`
    §"Mediant cohomology functor (count level)" — full
    formal statements + K_{4,3} marquee
  · `theory/essays/stern_brocot_as_universal_lattice.md` —
    the Stern-Brocot tree as the universal sample space
  · `theory/essays/c_counter_as_layer_count.md` — c-counter
    decouples from (NS, NT) lattice position
