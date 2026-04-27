# 03 — Simplex Geometry & Hinges

**Tier:** T1
**Status:** Closed for combinatorial counts; passing 4/27 standard.
**Lean:** `Physics/SimplexCounts.lean`, `Physics/FaceTerms.lean`,
`Physics/FoccSpectrum.lean`.

## Best current statement

Once d = 5 is fixed (Ch. 02), the geometric content of 213 lives on
the boundary of the 4-simplex Δ⁴ in ℂ⁵. Counts of k-dimensional faces
and hinge structures supply the combinatorial integers from which
physical observables are assembled.

### Simplex counts (`SimplexCounts.lean`)

For d = 5:

```
C(5, 0) = 1     vertices
C(5, 1) = 5     edges from a vertex
C(5, 2) = 10    pair channels
C(5, 3) = 10    Hodge-dual triples
C(5, 4) = 5     hinge faces
C(5, 5) = 1     volume cell
```

Hodge duality C(5,2) = C(5,3) = 10 is the **lattice version** of
electroweak duality; it forces NS = 3 channel structure and matches the
generation count Discovery (3 generations from C(5,2) modulo 1
diagonal).

### f_occ spectrum (`FoccSpectrum.lean`)

The 10 pairs admit a rational occupation spectrum:

```
f_occ = {1/5, 1/4, 1/3, 1/2, 1/1, 1/2, 1/3, 1/4, 1/5, 1/1}
```

(10 entries, no transcendentals.) This rational spectrum replaces the
integer-step quantum number assignments of standard quantum mechanics
and feeds directly into the BaselBound chain (Ch. 05).

### Hinge structure

Hinges (codim-2 simplices) carry the **deficit angle** δ_h that
replaces ℝ⁴ curvature in 213's Regge-style discrete gravity. δ_h is
signed — the sign carries orientation, not arithmetic negation
(connects to the cohomological framework of Ch. 14).

## 213 sharpening

- "Why ζ(2) appears in coupling running" → answer (partial): the f_occ
  spectrum sums to a rational bracket [S(N), upper(N)] that contains
  ζ(2) = π²/6, and the bracket tightens with N (`BaselBound.lean`).
- "Why C(5,2) = 10" → answer: forced by d = 5 atomicity and Pascal.
- "Why three generations" → answer (partial): 10 pairs / 3 channels
  with diagonal absorption; depends on the Discovery 1 photon kernel.

## Open / next

- Bracket tightening for ζ(2): currently [49/36, 183/108] at N=3,
  width ~0.6. Phase 4 marathon target: width < 10⁻⁴.
- Lift hinge deficit angle into a Lean-internal definition currently
  living only in narrative (drlt-book ch04–ch06).
- Decide whether `f_occ` is *the* spectrum or one representative of a
  family — uniqueness up to symmetry currently unproven.

## Sources

- `papers/paper6_simplex_coupling.tex`
- `papers/drlt-book/chapters/ch04_simplex_geometry.tex`
- `papers/drlt-book/chapters/ch06_geometry.tex`
- `lean/E213/Physics/SimplexCounts.lean`
- `lean/E213/Physics/FoccSpectrum.lean`
