# Synthesis interlock map

Three synthesis essays — `c_counter_programme_closure.md` (5
directions on K_{NS, NT}^{(c)} cohomology),
`p_orbit_closure_master.md` (6 phases on the Lucas-Pell trace
orbit), `layer_multiplication_pattern.md` (3 instances of one
proof shape) — each describe a closure of the framework, and
each names its own structural skeleton.  They were written
independently and stayed independent.  This essay fixes that
by tabulating the explicit correspondence: which c-counter
direction corresponds to which P-orbit phase, and how both
realise the layer-multiplication pattern.

## The unifying frame

The framework has two parallel closure axes:

  · **Cohomology axis** (graph side): K_{NS, NT}^{(c)} bipartite
    multigraphs, parametric in `(NS, NT, c)`.  Closure = "the
    c-counter is a structural layer count, not a depth
    parameter".
  · **Algebra axis** (Möbius side): P = [[2, 1], [1, 1]] ∈
    SL(2, ℤ), parametric in `(k : ℕ)`.  Closure = "the P-orbit
    Lucas-Pell trace ring exhausts framework-natural integers".

Both axes pass through the same atomic anchor
`(NS, NT, c, d) = (3, 2, 2, 5)`.  Both close by the same proof
shape (invariant + offset translation + cancellation lemma).
The interlock between them is the symmetric structural fact
the framework has been pointing at.

## Direction-by-direction correspondence

| c-counter direction | Role | P-orbit phase | Role |
|---|---|---|---|
| A — universal `(NS, NT, c)` framework (`EnrichedKNSNTc` master capstone) | parametric universality via `PairEnum NS` + `psi_layer_param` | Phases 1–2 — `CharPolySelf` (Cayley-Hamilton) + `POrbitRing` (12-prime ring catalogue) | seed + ring generation; the recurrence anchor |
| B — arbitrary-m bilateral kill (`9·m` offset cancellation, `NatBeqHelpers`) | per-layer uniformity through index translation | Phase 3 — `OrbitForcing` (Pell-Lucas recurrence coefficients forced from atomic seeds) | uniqueness of the recurrence step from atomic data |
| C — cup-image dual span (codim ≤ c via PRIMARY cup-image + `nine_block_disjoint`) | matching upper bound; cross-layer vanishing | Phases 4–5 — `PeriodDepthBounds` (depth-tagged primes up to 97) + `CrossProductAxes` (`CrossAddress` schema) | depth-bounded placement of every mod-p period in the ring |
| E — Stern-Brocot mediant Vandermonde (`binom_add_2` + V/E/F decompositions + `mediant_cohomology_functor_capstone`) | count-level functoriality over mediant | Phase 5 — `CrossProductAxes` (triple-axis address: bipartite, tripartite, P-orbit) | same Stern-Brocot mediant lifting traces to depth in P-iteration |
| T — bipartite-tripartite self-containment (V32LocalSignature positive + V32V213CohomologyBridge negative) | atomic-level duality preserved, cohomology-level duality broken | Phase 6 — `Cohomology/Tripartite/V213ShadowProjection` (Massey shadow vanishes; external tripartite closure negative confirmed) | cohomology-level test of tripartite extension; same negative verdict from a Massey angle |

The table is not an analogy.  Each row is the same structural
fact in two surfaces.  Direction A and Phases 1–2 both build
the parametric object from atomic seeds; Direction B and
Phase 3 both prove uniformity through cancellation; Direction
C and Phases 4–5 both bound the depth needed to span the
closure; Direction E and Phase 5 both lift the Stern-Brocot
mediant to a numerical decomposition; Direction T and Phase 6
both check whether an external extension recovers the
internal cohomology (it does not — verdict negative on both
sides).

## How the shared proof shape sits across all five rows

`layer_multiplication_pattern.md` names the shape:

  · invariant at a base level
  · offset translation indexing parallel copies
  · cancellation lemma absorbing the offset

Reading down the table column-by-column:

  · **Base level**: K_{3, 3} simple complex (cohomology axis) /
    L(0) = NT, L(1) = NS (algebra axis).
  · **Offset translation**: `m : Fin c` shifting `starS i 0 ↦
    starS i m` via `9·m` (cohomology) / `k : ℕ` shifting
    L(k+2) via Cayley-Hamilton matrix recursion (algebra) /
    `(NS, NT)` shifting via mediant decomposition (count
    Vandermonde).
  · **Cancellation lemma**: `nat_decide_add_left_assoc{1,2}`
    on `9·m` (cohomology) / `P^(k+1) = P · P^k` (algebra) /
    `binom_add_2` + `add_mul_pure` (count).

The cancellation lemmas live at three different
infrastructure layers (`NatBeqHelpers` / `Px/CharPolySelf` /
`Combinatorics/Binomial`) precisely because each closure
chose the cancellation that fit its surface.  The shapes
agree; the surfaces differ.

## What this collapses for the reader

Without this map, the three synthesis essays read as parallel
narratives — each closes its own programme, each names its
own shape, each cross-references the others without saying
HOW they correspond.  A reader who finishes
`c_counter_programme_closure` and then opens
`p_orbit_closure_master` has to re-derive the parallel by
hand.

With this map, every direction has a named phase counterpart
and every phase has a named direction counterpart.  The
"same-shape parallel" claim in
`c_counter_programme_closure.md` §"Same-shape parallel:
P-orbit closure" becomes a checked correspondence, not an
appeal to similarity.

## The thing you can point at

Five rows of the table above.  Each row is a Lean theorem
pair (one on each axis) plus a structural correspondence
statement.  No new Lean code is required for the map itself;
the correspondence is by inspection of theorem signatures
and proof shapes.

The deeper claim — that the cohomology axis and the algebra
axis are not merely parallel but **dually generated by P** —
remains open at the framework level.  Phase 5
(`CrossProductAxes`) defines `CrossAddress` as the candidate
triple-axis schema (bipartite ⊕ tripartite ⊕ P-orbit);
elevating this from address to functor would close the
duality.

## Cross-references

  · `theory/essays/c_counter_programme_closure.md` — five
    directions, this essay's column-1 source
  · `theory/essays/p_orbit_closure_master.md` — six phases,
    this essay's column-3 source
  · `theory/essays/layer_multiplication_pattern.md` — the
    proof shape underlying every row
  · `theory/essays/disjoint_layers_as_direct_sum.md` —
    categorical reading of the cohomology axis
  · `theory/math/cohomology/k_nm_c_classification.md` —
    chapter hosting Directions A/B/C/E in formal detail
  · `theory/math/mobius213_p_orbit_closure.md` — chapter
    hosting Phases 1–6 in formal detail
  · `theory/math/cohomology/tripartite_self_containment.md` —
    Direction T + Phase 6 cross-frame verdict
