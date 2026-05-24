# G140 — Non-vacuous Massey search at K_{3,2}^{(c=2)}

**Branch**: `claude/cohomology-marathon-qOxOX` (Phase 13 of G139 marathon).
**Status**: Active research.  Multi-agent investigation in flight.

## Problem framing

Phase 12 (G139-LL) proved that the Massey triple `⟨ω, ω, ω⟩`
at the K_{3,2}^{(c=2)} multi-5-cell substrate is **explicitly
zero** despite the non-vacuous landing space `H⁵ ≅ ℤ/2`.

**Structural obstruction**: ω = (1, 1, 1) is the constant-true
face cochain.  Any face-pair cup-evaluation gives `true`.  Both
Massey summands `b ⌣ ω` and `ω ⌣ b` produce `(true, true)`
diagonally; the xor collapses to `(false, false)`.

This G140 investigation asks: what Massey shape can be
**non-vacuous** at K_{3,2}^{(c=2)} (or close relatives)?

## Shape inventory

### Shape A — 4-fold Massey ⟨a, b, c, d⟩ at H¹⁴

Next-order obstruction beyond triple Massey.  Lands in
`H^(4-2) = H²`.  Defining-system requires triple-Massey
admissibility for ⟨a, b, c⟩ and ⟨b, c, d⟩.

### Shape B — H¹-based triple ⟨a, b, c⟩ at H¹³ → H²

`H¹(K_{3,2}^{(c=2)}) = (ℤ/2)⁶` with multiple basis classes.
Cup `H¹ × H¹ → H²` admits admissible triples; Massey
representative is non-trivial when not in the indeterminacy
ideal `a · H⁰ + H⁰ · c`.

### Shape C — Steenrod-style cup_i Massey

`Sq¹(ω) = δ²ω` at C³ (from G132 cup-ladder).  Massey via
cup_1 lifts to higher-degree landing space.

### Shape D — Multi-4-cell extension (break diagonality)

Current multi-5-cell extension has diagonal `δ⁴_multi`.  A
**multi-4-cell** extension (two σ⁴ cells with different
attaching) could break diagonality of `δ³`, breaking the
Massey-zero collapse.

### Shape E — Different graph (K_{3,3}, K_{m,n} variants)

Test the framework on related bipartite multigraphs with
richer cohomology.

## Research dispatch

Two parallel agents:

  · **Agent 1**: Computational H¹ × H¹ cup-product
    enumeration on K_{3,2}^{(c=2)}; Massey-admissible triple
    search; explicit non-vacuous Massey computation.
  · **Agent 2**: Theoretical analysis of shapes A-E;
    structural conditions for non-vacuous Massey; tractability
    ranking for Lean formalization.

## Agent 1 — H¹ × H¹ × H¹ → H² enumeration: complete

**Verdict**: under the "first-edge × opposite-edge" cup proposal,
all 83 Massey-admissible ordered triples yield ZERO Massey class.
Furthermore, the proposed cup **does not even descend to
cohomology** — 9 failure pairs where `[α] = 0` but `[α ⌣ β] ≠ 0`
in H².

### Key findings

**Cup sparsity**: the proposed cup reads only 4 of 12 edge
coordinates (`a[0], a[4]` on the left; `b[6], b[10]` on the
right).  The H¹ × H¹ → H² cup table:

```
      h0 h1 h2 h3 h4 h5
  h0 [ 0  0  0  0  0  0 ]
  h1 [ 0  0  0  1  0  1 ]
  h2 [ 0  0  0  0  0  0 ]
  h3 [ 0  0  0  0  0  1 ]
  h4 [ 0  0  0  1  0  0 ]
  h5 [ 0  0  0  1  0  0 ]
```

Only 6 non-zero entries out of 36.  Columns h0, h1, h2, h4 and
rows h0, h2 forced to zero by sparsity.

**Admissible triples**: 83 of 120 ordered (a, b, c) with
`[a⌣b] = [b⌣c] = 0`.

**Massey representative**: ALL 83 triples yield representative
class = 0 in H².

**Structural cause**: the admissibility constraint `a⌣b = b⌣c
= 0` plus the bilinear sparsity (4-coordinate dependence)
forces the Massey representative `a' ⌣ c + a ⌣ c'` into
`im(δ¹) = span{(1,1,0), (1,0,1)}` regardless of cobounding-chain
choice.

### Cup-descend failure

Sample failure pair:
  · α = δ(S₀-indicator) = (1,1,1,1,0,…) — a COBOUNDARY,
    representing 0 in H¹.
  · β = h₃ = (0,0,0,0,1,0,1,0,…) — a cocycle.
  · α ⌣ β = (1, 0, 0) ∉ im(δ¹).
  · This represents `[ω] ≠ 0` in H², so the cup is NOT
    well-defined on cohomology classes.

### Agent 1 recommendation

Either:
  · (a) **Redefine cup** with full Alexander-Whitney symmetric
    form (cyclic averaging over face boundary).  Over F_2 the
    "averaging" must be sum-based, not divisional.
  · (b) **Extend to 3-skeleton** — fill 3-cell with boundary
    `[face_0, face_1, face_2]` (already done in
    `Filled3CellExtension`).  Then C³ exists, Leibniz at chain
    level becomes well-defined, and H³ may carry non-vacuous
    Massey classes.

## Cross-references

  · `theory/math/cohomology/k32_higher_cohomology.md` — chapter
    with the Massey obstruction (Phase 12 update).
  · `lean/E213/Lib/Math/Cohomology/Bipartite/MasseyTripleOmega.lean`
    — the obstruction Lean source.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/Filled5CellMultiExtension.lean`
    — non-vacuous H⁵ substrate.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/H1K.lean` — H¹
    classifier infrastructure.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/Filled3CellCohomology.lean`
    — face boundaries + face_dependence.
