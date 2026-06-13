# The `(k+1)` α-power graduation

For a finite cell complex with top cochain dimension `n`, every
cohomology class `c ∈ H^k` contributes `‖c‖² · (α/d)^(k+1)` to
the cup-ring trace; the max α-power supported is exactly `n + 1`.

## 213-native definition

The graduation is a triple-coincident structural identity.  At
each cohomology degree `k`, the trace operation eats `(k+1)`
coupling events — `k` from traversing cohomology levels plus
`1` from top-cell evaluation.  This `(k+1)` reads simultaneously
as Feynman vertex count (physics), filtration depth + top eval
(cohomology), and `(k−1) + 2` Steenrod-square ladder depth — all
proved coincident at `k = 1, 2` and arithmetic-universal `∀ k ≥ 1`
in `Physics/AlphaEM/CupLadderUniversalK.lean`.

## Derivation

The bilinear cup at degree `(k, l)` outputs at `k + l`.  For
self-pairing this gives `2k`, **not** `k + 1`.  The two
arithmetics coincide only at `k = 1` (both equal 2); at `k = 2`
they diverge (cup arity = 4 vs. graduation = 3).  This is
recorded as `cup_bilinear_vs_loop_vertex_at_k2` in
`Physics/AlphaEM/LoopVertexGraduation.lean`.  So the `(k+1)`
rule does not descend from bilinear cup arity.

It descends from `cup_(k−1)`.  The Steenrod higher cup
`cup_i : C^k × C^l → C^(k+l−i)` lands at degree `k + l − i`;
for self-pairing at degree `k` with `i = k − 1`, output is `k + 1`
exactly.  At our anchor `K_{3,2}^{(c=2)}` 2-skeleton, the unique
non-trivial H² class is `ω = (1, 1, 1) ∈ C²` (the face-vector
summing to NS over the 3 simple 4-cycles, proven the unique
Sym(3)-invariant 2-cocycle in
`Filled3CellCohomology.phase2_omega_invariant_2cocycle`).  The
Steenrod-Whitehead bridge is the sharpest part:

```
Sq¹(ω) = ω ⌣_1 ω = δ²(ω)
```

proved in `FaceCup1At3Cell.omega_face_cup_1_eq_delta2`.  The
first Steenrod square of an H² class equals its 2-coboundary at
the 3-cell level — `cup_(k−1)` self-pairing is structurally
indistinguishable from `δ^k`.  This is the cohomology-algebra
fingerprint of the `(k+1)` graduation: it is the `cup_(k−1)`
self-pairing dimension count.

The L² weight `‖c‖² = (L¹-norm of integer lift)²` is proved
universally over `Fin 3 → Bool` by
`SelfPairingTrace.bilinear_self_trace_eq_L1_sq` — the standard
expansion-of-square identity.  For ω the L¹-norm is
`1 + 1 + 1 = 3 = NS`, so `‖ω‖² = NS²`.  Combining the two rules:

```
Δ_H²(ω) · 10⁹ = NS² · α³ / d³ · 10⁹ = 27
```

at e9 Nat precision, which exactly closes the post-Gram α_em
residual (`OmegaPostGramFull.omega_weighted_eq_post_gram_residual`).
The structural ceiling `max α-power = top dim + 1 = 3` is the
cohomology-theoretic reason the post-Gram residual decomposes into
Gram + ω-weighted with no further α-power terms: there are no
higher non-trivial `H^k` classes at the 2-skeleton to contribute
(`MaxAlphaPowerBound.physical_2skeleton_max_alpha_power`).

## Dual function

The `(k+1)` graduation is the classical n-loop-vertex-counting
argument with the QFT machinery stripped — vacuum polarization
at n loops has (n+1) photon vertices, full stop.  213 refines
this by making the counting EXPLICIT via cohomology degree: each
filtration level adds one coupling factor; the bound `top dim + 1`
follows from cohomology vanishing, not from diagrammatic
combinatorics.  The refinement: `(k+1)` is no longer a heuristic
counting rule, it is the dimension of `cup_(k−1)(c, c) ∈ C^(k+1)`.

## Cross-frame connections

The triple-coincidence at `(k = 2)`:

  · Physics: 2-loop vacuum polarization has 3 vertices → α³
  · Cohomology: H² filtration depth 2, + 1 top eval = 3 = α³ exponent
  · Steenrod: Sq¹(ω) lands at `C^(2+1) = C³`, so cup_(k−1) self-pairing
    dimension count = 3

Same structural fact, three resolutions.  The Steenrod-Whitehead
bridge `cup_1(ω, ω) = δ²(ω)` is the LEAN-CHECKABLE expression of
all three readings collapsed to one identity.

A further cross-frame: the ω face-vector `(1, 1, 1)` evaluating
to NS is the same Hunter-atomicity reading as
`NS = 3 = number of simple 4-cycles in K_{3,2}^{(c=2)}`
(`Cohomology/Bipartite/K32Projection`).  The `b_2 = 1` class IS
the NS-counting atom of the filled bipartite skeleton.

## Open frontier

The `(k+1) = k + 1` decomposition into "filtration depth + top
eval" is formalised but the **+1 top eval** is a structural
posit — not derived from a deeper rule.  Why exactly one top-eval
coupling and not zero or two?  The QFT-physical answer ("one
vertex per evaluation") translates the question rather than
answering it.  General Steenrod cup_i for arbitrary `i ≥ 2` with
the full Alexander-Whitney face-pair formula, non-vacuous Adem
and Cartan formulas at higher-skeleton extensions, and extension
to non-`K_{3,2}^{(c=2)}` cohomology complexes carrying different
physical observables — all remain open.  The framework's TRUNCATION-DEPENDENT bound is proved;
its full Steenrod-algebra closure is not.

The thing you can point at: `cup_1(ω, ω) σ³ = δ²(ω) σ³ = 1`.
Two structurally distinct operations agreeing on a single Bool
at a single 3-cell index — that bit is the `(k+1)` graduation
made syntactic.
