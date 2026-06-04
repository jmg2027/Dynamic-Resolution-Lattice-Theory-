# The c-counter programme: five-direction closure

The c-counter programme started as a single question — "where
does `c` show up in `K_{NS, NT}^{(c)}` cohomology?" — and
unfolded into a five-direction structural closure.  The
disjoint-layer direct-sum decomposition (`disjoint_layers_as_direct_sum.md`)
provided the categorical frame; the five directions filled
in the parametric universality, the per-layer uniformity, the
upper bound, the mediant functor, and the bipartite-tripartite
self-containment.  All five close at the structural level, and
they close jointly — each was needed to make the others speak.

## The five directions

### Direction A — universal `(NS, NT, c)` framework

V33EnrichedParametric closed K_{3,3} for all `c : Nat`; the
universal framework `Parametric/EnrichedKNSNTc.lean` lifts to
generic `(NS, NT)` via `PairEnum NS` + `psi_layer_param`.  The
Q-decomposition `qT_param`, `qS_param` factor the kill through
the t-fold / s-fold of `face_boundary_param`, dodging the
infeasible `2^(NS · NT · c)` per-instance case-bash.  The
**parity classification** splits closures into two branches:
even-NS / even-NT closes via uniform foldXor parity; odd-NS
closes via vertex-excluding ψ (`universal_kill_for_odd_n`).
`master_Knn_c_counter_resolved`: codim ≥ c at every
`K_{n, n}^{(c)}` for `n ∈ {3, 4, 5, 6}`, all c.

### Direction B — arbitrary-m bilateral kill

V33EnrichedParametric §20 extended `psi_layer_kills_cupOpp_*_at_bottom`
from `m = ⟨0, _⟩` to every `m : Fin c`.  Mechanism:
`starS c i m` and `incidT c j m` at same-layer
`edge_idx c i' j' m` reduce to **layer-independent triple Bool
disjunctions** after cancelling the common `9·m.val` offset.
The cancellation lives in `Meta/Nat/Beq213.lean`:
`nat_decide_add_left_assoc{1,2}` cancels the `9·m.val` offset
on the `==`-surface form emitted by `starS` / `incidT`,
`nat_add_left_cancel_pure` is the propext-free Nat
left-cancellation core.  After the offset cancels, the
6 / 9-edge β case-bash that closed bottom-layer kill runs
identically for every layer.

The `9·m.val` cancellation is the proof-level shadow of the
disjoint-layer direct-sum decomposition: every layer is a
translate of layer 0 along the offset, and the cancellation
absorbs the translate.

### Direction C — cup-image codim upper bound

V33EnrichedParametricDualSpan packages the `codim ≤ c` matching
half.  Three structural pieces:
ψ-linearity (`psi_layer_linear`) makes ψ_m an F₂-linear map;
surjectivity (`psi_layer_weighted_e_sum`) realises every target
ψ-vector via `Σ_m (b m) · e_face_layer m`; canonical decomposition
splits every v into a `weighted_e_sum` part + a residual in the
joint ψ-kernel.

**Why PRIMARY cup-image**: by bilinearity, full cup spans
`EnrichedFaceVal c` entire — `ψ_0(e_0 ∪ e_4) = true`
(`psi_layer_arbitrary_cup_not_kill`).  So the inductive
`InPrimaryCupSpanPlusBoundary` admits only δ¹σ, starS-cup,
incidT-cup, and XOR.

**Cross-layer vanishing unconditionally closed** via
`nine_block_disjoint` (`Beq213`): edge indices
`9·a + r` form disjoint blocks for distinct layers, so
`starS i m` evaluates to false on every layer-m' edge for
`m' ≠ m`, and the cup `cupOpp(starS i m, β)` vanishes layer-
m' face-by-face.  `psi_layer_{starCup,incidCup}_cross_layer`
is the XOR of 9 zeros.

`parametric_dual_span_capstone`: c ψ-discriminators SPAN the
dual of `EnrichedFaceVal c / InPrimaryCupSpanPlusBoundary`
(conditional capstone — now discharged unconditionally).
`primary_cup_span_soundness_c1`: at c = 1 the on-layer
hypothesis collapses (Fin 1 forces `m = ⟨0, _⟩`) — gives
unconditional `InPrimary ⊆ joint ψ-kernel` at single-layer
K_{3,3}.  `primary_cup_span_soundness_all_c` extends EASY to
every c by chaining with Direction B's
`parametric_arbitrary_m_full_kill_capstone`.

**Per-layer completeness closed (2026-05-25)** at every c via
`V33EnrichedParametricDualSpanHard` + `…Lift`: 8 explicit
primary cup-product generators (`g_1 … g_8`) span the dim-8
ψ-kernel at single-layer K_{3,3}; `promote_face`/`promote_edge`
lift each generator to layer m of `InPrimary c`, preserved
constructor-by-constructor (including the new `cong` constructor
that handles pointwise-equality bridging without `funext`);
`xor_aggregate` over `Fin c` reconstructs v.
`joint_psi_kernel_subset_primary` discharges the HARD direction
at every c.  Unconditional capstones
`parametric_dual_span_unconditional` +
`codim_upper_bound_unconditional` close `codim = c` at every
Stern-Brocot position against the PRIMARY cup-image.  See
`theory/essays/cohomology/per_layer_completeness_constructive_closure.md`.

### Direction E — mediant cohomology functor (count level)

The Stern-Brocot mediant `(NS₁, NT₁) ⊕ (NS₂, NT₂) =
(NS₁+NS₂, NT₁+NT₂)` lifts to **Vandermonde decompositions**
of every K_{NS, NT}^{(c)} cell count
(`MediantCohomologyFunctor.lean`, 22 PURE):

  · vertex 2-term, edge 4-term, face factored-Vandermonde²
    (9 products)
  · `binom_add_2` (combinatorial heart)
  · K_{4,3} = K_{1,1} ⊕ K_{3,2} marquee at c = 2

See `vandermonde_mediant_counts.md` for the dedicated
essay.

### Direction T — bipartite-tripartite self-containment

V32LocalSignature (positive: (2, 1, 3) multiset at every
vertex, edge, face of K_{3,2}^{(c=2)}) + V32V213CohomologyBridge
(negative: K_{2,1,3} has b₁ = 0, cannot host the bipartite
b₁ = 8 cohomological content).  See
`bipartite_tripartite_self_containment.md` and chapter
`tripartite_self_containment.md`.

## How the five directions interlock

| Direction | Closes for | Requires |
|---|---|---|
| A | every (NS, NT, c) | parity classification |
| B | every layer m | A's disjoint-layer indexing |
| C | matching upper bound | B's on-layer kill |
| E | count Vandermonde | Stern-Brocot reachability |
| T | self-containment | V32Betti + V213Betti |

A provides the parametric framework; B specialises A's
disjoint-layer fact to a per-layer uniform kill; C uses A's
ψ-functional + B's per-layer kill to span the codim dual; E
lifts Stern-Brocot to count Vandermonde; T uses V32Betti's
b₁ = 8 (a count fact about cycle space at the canonical anchor)
to refute external tripartite extension.

The five directions are not independent — they are
**aspects of a single structural closure** of the disjoint-layer
direct sum.  The reframing "c is a layer count, not a depth
parameter" forces all five into the same closure pattern.

## Same-shape parallel: P-orbit closure

A structurally identical reframing happens on the algebraic
side.  The 36-species atomic catalog faced a "non-atomic prime
7" appearing in mod-13 and mod-29 periods.  The P-orbit
closure programme (`mobius213_p_orbit_closure.md`) reframes
this as: 7 = L(2) = trace(P²), the depth-2 trace in the
Lucas-Pell sequence generated by `P = [[2,1],[1,1]]`.  The
naturalness boundary moves from depth-0 atomic
(`⟨{NT, NS, d}⟩_ℤ`) to depth-ω P-orbit
(`⟨{L(k)} ∪ {NT, NS, d}⟩_ℤ`), with the atomic catalog being
the depth-≤-1 sub-closure.

The P-orbit closure programme also closes in multiple
directions (CharPolySelf, POrbitRing, OrbitForcing,
PeriodReciprocity, PnFibonacci, CassiniUniversal) and
yields `naturalness_closure_master` / `p_orbit_closure_master`
analogous to the c-counter `master_Knn_c_counter_resolved`.
See `p_orbit_closure_master.md` for the dedicated essay.

The structural pattern is the same: a parametric closure
(c-counter codim ≥ c / P-orbit depth-ω) supersedes a
narrower computational invariant (Massey depth at fixed
complex / atomic-only ring) as the framework's natural
boundary.

## The thing you can point at

Three master theorems jointly close the programme:

  · `master_Knn_c_counter_resolved` — Direction A capstone
  · `parametric_arbitrary_m_full_kill_capstone` — Direction B
    capstone
  · `parametric_dual_span_capstone` — Direction C capstone

Plus `mediant_cohomology_functor_capstone` (Direction E) and
`self_containment_cohomology_verdict` (Direction T).

Five Lean theorems.  One question.  The c-counter sits in the
disjoint-layer direct-sum decomposition; each direction is one
face of that single structural object.

## Open frontier (residual)

Per-layer completeness — closed (2026-05-25): the last piece
for unconditional Direction C is discharged at every c by
`joint_psi_kernel_subset_primary`.  Remaining items:

  · **Cochain-level mediant functor**: count-level closed,
    cup-product algebra lift open.
  · **Massey-class lift of the mediant**: do K_{4,3} Massey
    witnesses factor through K_{1,1} ⊕ K_{3,2}?
  · **Pell-orbit extensions**: (8, 5), (5, 4), (7, 4), (13, 8)
    — next Stern-Brocot layer.  Concrete witnesses, structural
    cohomology theorems transport via Direction A.

## Cross-references

  · `theory/math/cohomology/k_nm_c_classification.md` —
    central chapter hosting the formal closures
  · `theory/math/cohomology/tripartite_self_containment.md` —
    Direction T
  · `theory/math/algebra/mobius213_p_orbit_closure.md` — parallel
    P-orbit closure programme
  · `theory/essays/cohomology/c_counter_as_layer_count.md` — the reframing
    "c as layer count" that makes the five-direction closure
    possible
  · `theory/essays/cohomology/disjoint_layers_as_direct_sum.md` — the
    categorical reading underlying all five directions
  · `theory/essays/cohomology/multiplicity_layer_uniformity.md` —
    Direction B essay
  · `theory/essays/cohomology/cup_image_dual_span.md` — Direction C essay
  · `theory/essays/cohomology/vandermonde_mediant_counts.md` — Direction E
  · `theory/essays/p_orbit/bipartite_tripartite_self_containment.md` —
    Direction T
  · `theory/essays/p_orbit/p_orbit_closure_master.md` — parallel
    P-orbit programme synthesis
