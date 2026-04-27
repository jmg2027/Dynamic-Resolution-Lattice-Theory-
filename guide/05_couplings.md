# 05 — Coupling Constants

**Tier:** T2 (classical adequate; 213 sharpens individual brackets)
**Status:** Partial — α_GUT and α_em closed as rational brackets, not yet
to ppm width. Headline 1/α_em = 137.036 *not yet* 4/27-passing.
**Lean:** `Physics/AlphaGUT.lean`, `Physics/AlphaEM.lean`,
`Physics/AlphaEM137.lean`, `Physics/BaselBound.lean`.

## Best current statement

The unified coupling constant is, classically:

```
α_GUT = 6 / (25 π²)
1/α_GUT = d² · ζ(2) = 25 · π²/6 ≈ 41.123
```

In 213, ζ(2) is replaced by the rational bracket `[S(N), upper(N)]`
generated from the f_occ spectrum (`BaselBound.lean`). At N = 3:

```
1/α_GUT ∈ [25 · 49/36, 25 · 183/108] = [1225/36, 4575/108]
                                     ≈ [34.03, 42.36]
```

This **strictly contains 41**, proven `by decide` (no real numbers, no
axioms). The bracket tightens monotonically with N.

### α_em chain (AlphaEM137.lean — honest tag)

The candidate formula:

```
1/α_em(bare) = 60 · ζ(2) + 30   (Weinberg sum)
1/α_em(IR)   = 10 π² + 30 + d²/NS + α_GUT/(NS+1)
```

At N = 10, the bracket contains 137 (proven `by decide`).
**Honesty tag in source:** the `d²/NS = 25/3` term is *conjectural
structural form*, plausible but not derived from the Raw axiom.

### α_3 (strong coupling, confined regime)

`Physics/PhotonKernel.lean` identifies 1/α_3 = b₁(K_{3,2}) = NS² − 1
= 8. This is closed and exact; it depends on Discovery 2 (photon =
cycle space of K_{3,2} bipartite graph).

## 213 sharpening

- ζ(2) → S(N) rational bracket: classical *transcendental* replaced by
  *finite rational interval*. Width is the open question, not the
  value.
- Three classical "paths" to α_GUT (simplex, RMT, coprimality) collapse
  into a single bracket-tightening problem.
- 1/α_3 = 8 is exact, derived from atomicity. No counterpart in
  classical QCD.

## Open / next (Open Problem #2 from HANDOFF.md)

- **Tighten α_em bracket to width < 10⁻⁴** at the headline value
  137.036. Estimated N ≈ 6×10⁵; not yet computed.
- **Derive d²/NS = 25/3 term from atomicity** rather than tagging
  conjectural. This is the structural-origin gap in `AlphaEM137.lean`.
- Extend Phase 4 chain to formally close the inequality
  `|1/α_em − 137.036| < 10⁻⁴` in a single Lean theorem.

## Sources

- `papers/paper2_frobenius_to_gauge.tex` (α_GUT three paths)
- `papers/paper4_zeta_beta.tex` (coupling running)
- `papers/paper6_simplex_coupling.tex`
- `papers/drlt-book/chapters/ch08_couplings.tex`
- `lean/E213/Physics/AlphaGUT.lean`, `AlphaEM137.lean`,
  `BaselBound.lean`, `PhotonKernel.lean`.
