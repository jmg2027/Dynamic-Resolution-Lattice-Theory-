# Session handoff

Branch: `claude/tier-1-1-psi-kernel-wnpIS`.  Built clean
(`cd lean && lake build`), 0 sorry, 0 external axioms.

## This session (2026-05-25)

Tier 1.1 — Per-layer ψ-kernel completeness — FULLY CLOSED
at every c ≥ 1.

  · HARD direction at c=1: 8 explicit primary cup-product
    generators `g_1 … g_8` spanning the dim-8 ψ-kernel at
    single-layer K_{3,3}.  Generators are cups of `starS`/
    `incidT` cocycles with single-edge cochains
    (`e_edge`).  Closed-form decomposition coefficients
    `b_1 … b_8` extracted from v's 9 face values; the (1, 0)
    position equation `v(1,0) = b_3 ⊕ b_4 ⊕ b_7 ⊕ b_8` is
    exactly `ψ_0(v) = 0`.  9 per-position lemmas verify
    pointwise equality; `cong` constructor (added to the
    `InPrimary` inductive) bridges to v as a function
    without `funext`.  `joint_psi_kernel_subset_primary_c1`
    in `V33EnrichedParametricDualSpanHard` (51 PURE).
  · ∀c lift via layer-promotion: `promote_face`/
    `promote_edge` (9-fold `cond` cascade — propext-free)
    transport each c=1 InPrimary witness to layer m of
    `InPrimary c`.  Preserved across all 6 constructors
    (zero, coboundary, starCup, incidCup, xor_add, cong)
    inductively.  `xor_aggregate` composes layer-m promotes
    into a full reconstruction of v.
    `joint_psi_kernel_subset_primary` and unconditional
    capstones (`parametric_dual_span_unconditional`,
    `codim_upper_bound_unconditional`) in
    `V33EnrichedParametricDualSpanHardLift` (21 PURE).
  · `codim = c` upper bound is now UNCONDITIONAL at every
    Stern-Brocot position against the PRIMARY cup-image.

## Boot order

  · `seed/AXIOM/05_no_exterior.md` §5, §8.4 — re-read every
    session start
  · `theory/INDEX.md` — book map
  · `lean/E213/ARCHITECTURE.md` — layer ring spec
  · `theory/PROMOTION_CRITERIA.md` — Hard / Soft gates

## What's closed (chapter level)

  · `theory/math/cohomology/k_nm_c_classification.md` —
    universal `(NS, NT, c)` cohomology framework
    (EnrichedKNSNTc) + codim ≥ c parametric + codim ≤ c
    dual-span (NOW unconditional at every c) + arbitrary-m
    bilateral kill (`9·m` cancellation in `NatBeqHelpers`)
  · `theory/math/cohomology/mediant_cohomology_functor.md` —
    Stern-Brocot mediant Vandermonde at the count level
    (V 2-term / E 4-term / F factored-Vandermonde²);
    K_{4, 3} = K_{1, 1} ⊕ K_{3, 2} marquee
  · `theory/math/cohomology/tripartite_self_containment.md` —
    K_{3, 2}^{(c=2)} local (2, 1, 3) signature at every point;
    K_{2, 1, 3} Betti (1, 0, 0); cohomology-level
    self-containment verdict (atomic preserved, b₁ breach)
  · `theory/math/mobius213_p_orbit_closure.md` — P-orbit
    naturalness boundary + structural forcing via
    `Theory/Atomicity/OrbitForcing` + Lucas-Pell recurrence
    + period reciprocity + n-Fibonacci + Cassini universal
  · `theory/essays/c_counter_programme_closure.md` —
    cross-cutting synthesis of the c-counter five-direction
    closure + same-shape parallel to P-orbit

## What's open (residual)

Per-layer completeness is closed.  Genuinely open structural
questions:

  · **Cochain-level mediant functor**: count-level Vandermonde
    closed; lifting to cup-product algebra (4 edge + 9 face
    sub-cells per mediant) is the next layer.
  · **Massey-class mediant lift**: do K_{4, 3} 4-fold Massey
    witnesses factor through K_{1, 1} ⊕ K_{3, 2}?
  · **Pell-orbit extensions**: (8, 5), (5, 4), (7, 4), (13, 8)
    — next Stern-Brocot layer.  Concrete reachable witnesses;
    structural cohomology transports via Direction A.
  · **n-prime P-orbit depth bound**: empirically D(p) ≤ 4 for
    p ≤ 97; asymptotic growth (O(log p)?) is open.
  · **Cup-product transport on V32LocalSignature**: does the
    (2, 1, 3) local signature persist under cup
    `H^k × H^l → H^(k+l)` at K_{3, 2}^{(c=2)}?
  · **Tier 1.2 — Arity c=2 Lean theorem**: missing 4th piece
    of atomic signature forcing.

## Companion specs

`seed/RESOLUTION_LIMIT_SPEC.md`,
`seed/THEOREM_METHODOLOGY_SUITE.md`,
`seed/META_SCAN_ARCHETYPES.md`,
`seed/CLOSED_FORM_SPEC.md`.  Per-conjecture catalogue at
`research-notes/G35_chiral_cup_ring_catalog.md` (§0.5 tracks
chapter promotions).
