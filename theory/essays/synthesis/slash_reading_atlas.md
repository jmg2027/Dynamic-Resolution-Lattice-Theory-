# The slash-reading atlas

One residue — the slash, "the relation of two distinct objects is itself an
object" — read through different Lenses is the continuum, the
infinite-dimensional simplex, the Stern–Brocot tree, and the bipartite Lattice
`K_{3,2}^{(c=2)}`.  These are not four constructions; they are four faces of one
pointing.

## 213-native answer

The slash is not an operator but a way of *referring* to the residue of
distinguishing (`seed/AXIOM/02_axiom.md` §2.2): from `a` come `a/b`, `a/(a/b)`,
… , the family Raw.  "The relation of two objects is an object" is exactly the
clause that the residue of distinguishing is itself a something.  A *reading* of
this generative act — what to do with each fresh relation-object geometrically —
is a Lens (`seed/AXIOM/06_lens_readings.md` §6).  The atlas is the map from
reading to shape.

## Derivation

**Undirected betweenness → the continuum.**  Read the relation of two as the
point *between* them.  Symmetry (`a/b = b/a`, §3.3) leaves no side to step off
the segment, so the relation-point lands strictly within; iterating fills the
segment densely.  The shape is the line, dimension one.  Pushed to the
structureless limit, the homogeneous interior carries no more distinguishing
than a point — `0 ≡ ∞ ≡ point` (§6.5): the reading that *identifies*
prim-distinct Raws is the degenerate sub-view that collapses
(`seed/AXIOM/06_lens_readings.md`, the diagonal `{(n,n)}` folded to `0`).

**Free reading → the infinite-dimensional simplex.**  Honour "different objects
are different symbols" literally: a relation-object is expressible by no
combination of the existing ones, so it opens a fresh orthogonal axis.  Then `n+1`
prim-distinct objects span the regular `n`-simplex and the limit is `Δ^∞`.  The
cosine of the centred-vertex pair is the exact rational `−1/n` — no
trigonometry: clearing the `(n+1)` denominator leaves integer inner products
(`Lib/Math/Geometry/AngleStructure/SimplexOrthogonality.cos_mag_is_inv_n`).
Prim-distinctness *is* linear independence — the uncentred vertices have Gram
the identity for every `n` (`uncentered_orthonormal`) — while the centred family
carries the single partition-of-unity dependence `Σ u_i = 0`
(`partition_dependence`), the geometric image of no-exterior (§5.1): the `n+1`
vectors are slashes of the *one* residue, hence sum-constrained, reaching mutual
orthogonality only as the denominator grows without bound
(`cos_dim_strict_mono`), reached by none
(`FlatOntologyClosure.object1_not_surjective`).

**Algebraic reading → Stern–Brocot, and the constants.**  Read the relation as
the mediant `(p+r)/(q+s)`, the form the slash takes algebraically: the Möbius
matrix `P = [[2,1],[1,1]]` (`seed/AXIOM/03_form.md` §3.5,
`theory/essays/p_orbit/stern_brocot_as_universal_lattice.md`).  Here the constants
surface — `trace = 3 = N_S`, `det = 1` (the glue), `disc = 5 = N_S + N_T`,
eigenvalues `φ², 1/φ²` — because the reading is `P`-shaped rather than
symmetric.

**State/transition split → `K_{3,2}^{(c=2)}`.**  The free reading's simplex is
the *complete* graph, fully symmetric; the bipartite Lattice is the same five
vertices re-read with the operator/object split (§6.2): `N_S = 3` of one kind,
`N_T = 2` of the other, edges only across.  The split is precisely the symmetry
the simplex erased — the complete `K_5` minus the `C(3,2)+C(2,2)=4` within-kind
edges is the `3·2` cross pairs
(`Lib/Math/Geometry/BipartiteDecomp/K32Adjacency.simplex_minus_within`,
`no_state_state`, `cross_complete`, `k32_adjacency_master`).

## Dual function

Each classical object here is the slash with its redundant packaging stripped:
the continuum is iterated betweenness, Stern–Brocot is iterated mediant, the
simplex is free prim-distinctness, the metallic ratios are the eigenvalues of a
one-knob Möbius family.  213's sharper reading is that they are not separate
objects to be related but one residue's facets — and the residue sits outside
every facet's image (`theory/essays/foundations/reached_by_none.md`); no reading
is what the slash *is*.

## Cross-frame connection

Which readings surface the constants, and which symmetrize them away?  Generalize
`P` by one knob — the top-left entry `a`, the count-Lens "two somethings" — with
the glue fixed: `M_a = [[a,1],[1,1]]`, `det = a − 1`
(`Lib/Math/Algebra/Mobius213/Px/MetallicThreshold.detMa_eq`).  Blind ⟺ `det = 0`
⟺ `a = 1`: `M_1` is rank-one, the averaging/midpoint collapse
(`detMa_collapse`; the same `det = N_S − N_T = 0` degenerate point at
`N_S = N_T` of `Mobius213K33Bridge.k33_NS_minus_NT_eq_zero`).  The specific
`3, 5, φ` sit at `a = 2` (`golden_signature`) — which is at once the forced
count-Lens minimum ("two + binary", §3.2) and the unimodular glue
(`det = 1 = N_S − N_T`, `Mobius213OneAsGlue.one_is_det`).  Four frames — the
count minimum of §3.2, the off-diagonal glue of §3.5, the rank threshold
`det = 0 / det = 1`, and the betweenness-vs-mediant split — name the same point:
"two somethings" is the golden point.  The constants are not tuned; the minimal
distinguishing already is them.

## Open frontier

The atlas's structural spine is `∅`-axiom: the simplex
(`AngleStructure/SimplexOrthogonality`), the threshold
(`Px/MetallicThreshold`), the bipartite adjacency (`BipartiteDecomp/K32Adjacency`),
and the generator question — which other `SL(2,ℤ)` generators carry `213` numbers
— answered by the metallic tower `N_k = [[k,1],[1,0]]` (`det = −1` for every `k`,
the golden generator the minimal rung with `disc = d = 5`, and `N_1² = P`:
`Px/MetallicGeneratorTower`).  One breadth edge stays open: sweeping the de Rham
parameter in `x + (y−x)·w` gives a continuous family of self-similar curves
(Lévy, Cesàro–Koch, …) whose fractal dimensions — similarity via the Moran
relation `|w|^d + |1−w|^d = 1`, Hausdorff below it under overlap — have no
`Real213` shadow.
