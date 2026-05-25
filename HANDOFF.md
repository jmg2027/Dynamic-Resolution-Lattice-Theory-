# Session handoff

Branch: `claude/research-essay-audit-Fl1pZ`.  Built clean
(`cd lean && lake build`), 0 sorry, 0 external axioms on
production critical path.

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
    dual-span (conditional + c = 1 unconditional + cross-layer
    unconditional) + arbitrary-m bilateral kill
    (`9·m` cancellation in `NatBeqHelpers`)
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

Genuinely open structural questions:

  · **Per-layer completeness** for unconditional `codim = c`:
    joint ψ-kernel ⊆ `InPrimaryCupSpanPlusBoundary`.  Reduces
    to a single-layer K_{3,3} dimension count (9-element face
    space modulo (im δ¹ + primary cup-image) has dim 1);
    layer-disjointness lifts to ∀c.
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

## Companion specs

`seed/RESOLUTION_LIMIT_SPEC.md`,
`seed/THEOREM_METHODOLOGY_SUITE.md`,
`seed/META_SCAN_ARCHETYPES.md`,
`seed/CLOSED_FORM_SPEC.md`.  Per-conjecture catalogue at
`research-notes/G35_chiral_cup_ring_catalog.md` (§0.5 tracks
chapter promotions).
