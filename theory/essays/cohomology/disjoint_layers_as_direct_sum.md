# Disjoint layers as categorical direct sum

The enriched 2-complex on `K_{NS, NT}^{(c)}` factors as a
categorical direct sum of `c` copies of the simple-cycle
complex.  Once the splitting is named, the c-counter
`codim ≥ c` becomes a one-line consequence — direct sums
preserve cohomology componentwise.

## 213-native answer

The enriched chain complex on K_{NS, NT}^{(c)} (mult-m face
cycles for `m ∈ Fin c`) splits as

```
C¹_enr = ⊕_{m ∈ Fin c} C¹_simple_m
C²_enr = ⊕_{m ∈ Fin c} C²_simple_m
δ¹_enr = ⊕_m δ¹_simple_m
```

Each `C^k_simple_m` is one copy of the simple-cycle complex on
the layer-m edge subset.  Distinct layers share no edges
(disjoint indexing), so the differential `δ¹_enr` has block
structure — no off-diagonal cross-layer terms.

Cohomology distributes through the direct sum:

```
H^k_enr        = ⊕_m H^k_simple_m
cup-image_enr  = ⊕_m cup-image_simple_m
codim_enr      = c · (per-layer codim) = c · 1 = c
```

## Derivation

The disjointness rests on the edge-indexing rule.  Edge index
`c·k + m` packs (layer `m`, cross-pair `k`) into one Fin:

```
edges at mult m = { c·k + m : k ∈ Fin (NS · NT) }
```

For `m ≠ m'`, `c·k + m ≠ c·k' + m'` (mod c distinguishes).
Hence the layer-m and layer-m' edge subsets are disjoint, and
the edge cochain space splits canonically:

```
C¹_enr ≅ ⊕_{m ∈ Fin c} C¹_simple
```

The face-cycle space similarly splits: layer-m face cycles use
only layer-m edges (the 4-cycle definition restricted to one
multiplicity).  The boundary map `δ¹_enr` therefore commutes
with the projection to layer-m components — block-diagonal.

The discriminator `ψ_m` is the projection-then-XOR functional
for layer m:

```
ψ_m(v) := XOR_{f ∈ layer-m faces} v(f)
```

`ψ_m` vanishes on every `δ¹_enr σ` whose layer-m part has the
right parity (and the layer-m-edge-in-(NS−1)(NT−1)-faces fact
makes this automatic).  `ψ_m` is non-zero on the single-face
indicator `e_face_(9m)` (one layer-m face).  And `ψ_m'` for
`m' ≠ m` evaluates `e_face_(9m)` to zero — Kronecker δ.

So `ψ_m` IS the projection-to-H²_simple_m functional composed
with the per-layer XOR class.  c such projections exist by
construction; they span a c-dimensional subspace of
`H²_enr / cup-image`.

## Dual function

This is not "the enriched complex happens to have a direct-sum
decomposition".  It is the operational content of "the c-counter
is a structural parameter, not a calculated invariant" — see
the companion essay `c_counter_as_layer_count.md`.

A calculated invariant (e.g. cup-image rank in a fixed complex)
depends on the entire complex's combinatorics.  A direct-sum
multiplicand (e.g. number of summands) reads off from the
PRESENTATION: count the disjoint blocks.  No computation.

The classical reframing the direct-sum reading absorbs: the
"c-dependent Massey depth" hypothesis (depth = c+2) treated c
as a calculation parameter inside one complex.  Once the
direct-sum structure is named, depth becomes constant (depth = 4
on every layer); only the NUMBER of independent witnesses
scales with c.  Computation moves from "what depth reaches the
extra dimensions" to "how many copies of the same depth-4
witness are stacked".

## Cross-frame connections

The direct-sum reading is the categorical realisation of three
seemingly distinct facts:

  · **Edge-disjointness** at the chain level
    (`c·(NT·i + j) + m` indexing).
  · **Massey witness independence** at the cohomology level
    (`eta_ab_layer m`, `eta_cd_layer m` parameterised over m).
  · **ψ-discriminator orthogonality** at the functional level
    (Kronecker δ pairing in
    `parametric_c_independent_h2_classes`).

All three are the same fact in three frames: the layer-m and
layer-m' sectors of K_{NS, NT}^{(c)} are *categorically
separated*.

The parametric Lean proof keeps the splitting INVISIBLE — the
abstract face value space `Fin 3 → Fin 3 → Fin c → Bool` is
defined as a function space, not a direct sum.  The
`omega`/`simp`/`funext`/`dite`-free proof works because the
splitting is concrete enough at the level of `decide` reduction:
for fixed `m, m'`, `decide (m.val = m'.val)` evaluates to the
Kronecker bool directly.

## Per-layer = per-`Pseq depth` ?

The disjoint-layers pattern hints at a deeper structure on the
Möbius P side: the Pseq orbit at depth k carries one "atomic
copy" of the (NS, NT) signature per iteration step.  Iterating
P is the Möbius analogue of stacking layers — `Pstep^k` builds
k independent depth-k samples of the seed.

This is the analogy that connects the c-counter direct sum to
the P-orbit closure of `mobius213_p_orbit_closure.md`: both
describe "stack k independent copies of an atomic structure" —
on the cohomology side as multiplicity layers, on the Möbius
side as P-iteration depth.  Whether they are literally the same
direct-sum decomposition (in some category) is an open
structural question.

## Open frontier

  · **Categorical statement**: write the layer splitting as
    a Lean theorem `enriched_complex_iso_direct_sum`
    (currently implicit in the parametric proof — making it
    explicit would clarify the structural content).
  · **Cup-image upper bound**: the direct-sum decomposition
    implies `codim ≤ c` from above, but proving equality needs
    showing that NO cross-layer cup product hits a previously
    unreached H²-component.  This is the conjectured equality
    `codim = c`.
  · **K_{NS, NT}^{(c)} analogue for ψ-discriminator**:
    the disjointness argument is graph-agnostic (only depends
    on the indexing rule).  Lifting `parametric_c_independent_h2_classes`
    from `NS = NT = 3` to general `(NS, NT)` requires symbolic
    `Nat.choose 2`-indexing — see frontier of
    `theory/math/cohomology/k_nm_c_classification.md`.

The thing you can point at:
`parametric_c_independent_h2_classes` — one Lean theorem whose
statement IS the direct-sum decomposition's cohomology
consequence, made formal at every `c : Nat`.  Read backwards,
the theorem says "the enriched complex's H² has at least c
independent classes outside cup-image" — the c summands of the
direct sum, each contributing its own non-coboundary class.

## Cross-references

  · `c_counter_as_layer_count.md` — companion essay on the
    reframing of c from depth to layer count
  · `theory/math/cohomology/k_nm_c_classification.md` —
    chapter hosting the parametric theorem
  · `research-notes/archive/G145_c_counter_structural_theory.md`
    §Insight 2 — original "Disjointness of edge sets is the
    master structural fact" statement
