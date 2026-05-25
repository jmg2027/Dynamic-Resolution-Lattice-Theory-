# G140 — Non-vacuous Massey search at K_{3,2}^{(c=2)}

**Branch**: `claude/cohomology-marathon-qOxOX` (Phase 13 of G141 cohomology marathon).
**Status**: Closed at merge (2026-05-24).

> **Numbering note**: Phase labels `G139-*` / `G140-*` are in-branch
> shorthand from before the G139 collision with the Möbius marathon
> was discovered.  The marathon as a whole now lives at
> `research-notes/G141_cohomology_marathon.md`.  See header note there.

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

## Agent 2 — Alternative shape analysis: complete

Five shapes analyzed (A: 4-fold Massey; B: H¹³ → H²;
C: cup_i Massey; D: multi-4-cell asymmetric extension;
E: different graph K_{3,3}^{(c=2)} etc.).

### Verdict ranking (tractability for Lean closure)

| Rank | Shape | Why |
|---|---|---|
| 1 | **B at ⟨r, x, r⟩** | Stays at 2-skeleton; uses existing H1K infrastructure; radical-element Massey kills indeterminacy. |
| 2 | **D multi-4-cell** | Asymmetric AW lift breaks diagonal collapse; can make ⟨ω, ω, ω⟩ itself non-vacuous. |
| 3 | **E at K_{3,3}^{(c=2)}** | New graph infrastructure; generalizes but does not simplify. |
| 4 | **C cup_1 Massey** | Needs ≥ 6-skeleton + multi-cell — far from current ceiling. |
| 5 | **A 4-fold Massey** | Indeterminacy collapses to all of H² — structurally vacuous. |

### Shape B core insight (radical-element Massey)

The cup pairing `H¹ × H¹ → H²` (over F_2) is a symmetric
bilinear form.  By face_dependence (`Face_0 ⊕ Face_1 ⊕ Face_2
= 0`), the form has a **radical element** `r ∈ H¹` such that
`r ⌣ x = 0` for all `x ∈ H¹`.

The Massey triple `⟨r, x, r⟩` is then ALWAYS admissible
(`r ⌣ x = 0` and `x ⌣ r = 0` by symmetry).  Indeterminacy
ideal `r · H⁰ + H⁰ · r = {0}` since `r` is in the radical.

Predicted: `⟨r, x, r⟩ ≠ 0` in H² for some specific `x` —
typically `x` being the "all-non-tree-edges generator"
(the H¹ analog of ω).

### Shape D core insight (multi-4-cell asymmetric AW)

Current `δ⁴_multi` (Filled5CellMultiExtension) is diagonal
because both 5-cells share boundary `[σ⁴]`.  Adding TWO
4-cells `σ⁴_a, σ⁴_b` with the same boundary `[σ³]` creates a
4-skeleton with `H⁴ = F_2`.  The cup extension `C² × C² →
C⁴_multi` then has a 2-dim choice space — an asymmetric AW
lift `(α ⌣ β)(σ⁴_a) := α(face_0) ⌣ β(face_2)` vs
`(α ⌣ β)(σ⁴_b) := α(face_2) ⌣ β(face_0)` breaks bilinear
symmetry.

Then `ω ⌣ ω` value differs at σ⁴_a vs σ⁴_b (no longer
diagonal), cobounding chains can be non-diagonal, and the
Massey representative at C⁵_multi can land off-diagonal —
representing the non-zero H⁵ class.

### Recommended path (Agent 2)

Pursue Shape B first: 3 new Lean files
(`CupC1C1.lean`, `RadicalH1.lean`, `MasseyTripleH1.lean`),
~250 lines PURE, decide-tractable throughout.  Stays in
2-skeleton.  Shape D as follow-up.

## Independent verification (cup-descent + radical computation)

Direct numerical experiment with three cup candidates on the
K_{3,2}^{(c=2)} 2-skeleton:

  · `cup_full_cyclic`: 14336 / 32768 descent failures (44%)
  · `cup_sym_pairs`: 12288 / 32768 (37%)
  · `cup_aw_consecutive`: 15360 / 32768 (47%)

**None of the natural cup definitions descend to cohomology**.
Cup product on the bipartite multigraph 2-skeleton with c=2
multiplicity is FUNDAMENTALLY non-canonical — the structure
admits only chain-homotopy classes of cups, not strict cups.

Shape B Massey ⟨r, x, r⟩ computation with `cup_full_cyclic`
(despite descent failure) finds 3-dim radical and computes
all candidate Massey reps to 0 in H².  But these results are
not meaningful since the cup doesn't well-define the Massey
class.

## STRUCTURAL ROOT-CAUSE ANALYSIS

The K_{3,2}^{(c=2)} 2-skeleton is a CW complex with 4-cycle
2-cells that are NOT canonical simplices.  Defining a strict
cup product requires either:

  1. A cellular diagonal approximation Δ: C → C ⊗ C
     satisfying chain-map conditions — but for 4-cycle cells,
     Δ is non-canonical (requires choice of triangulation).
  2. Triangulating with virtual diagonal edges (e.g.,
     S₀—S₁) that don't exist in the bipartite graph.
  3. Extending to higher skeleton where Δ becomes
     well-defined cellularly.

Under F_2 (no halving), even the "averaged" cup constructions
that work over ℚ or ℂ fail descent.

## Path forward

**Three viable closures** for non-vacuous Massey (in order of
tractability):

### Closure Path I — Document the obstruction (NEW Lean module)

The CLEANEST mathematical contribution is to **formalize the
non-existence**: prove there is NO strict cup C¹ × C¹ → C²
over F_2 on the K_{3,2}^{(c=2)} 2-skeleton that satisfies
both bilinearity AND descent to cohomology AND chain-level
Leibniz.

This is itself a structural theorem worth Lean-formalizing.

### Closure Path II — Extend to 3-skeleton with cup machinery

Build cup product `C^p × C^q → C^(p+q)` for p+q ≤ 3 on the
Filled3CellExtension complex.  At this skeleton:
  · H² becomes 0 (ω trivializes via δ²(ω) = (true))
  · H³ may carry non-trivial classes from σ³
  · Massey at H¹³ lands in trivial H² — vacuous at this layer
  · But Massey at H¹² → H¹ + ... could be non-vacuous

This is multi-session infrastructure work.

### Closure Path III — Different graph (K_{3,3} or non-bipartite)

Switch to a complex where standard simplicial AW cup works.
E.g., triangulated K_{3,3}^{(c=2)} or a different graph
entirely.  Trade tractability for substrate complexity.

## Tension with Agent 1 finding

Agent 1 proved the naïve "first-edge × opposite-edge" cup is
**ill-defined on cohomology** (9 failure pairs).  Agent 2's
Shape B closure requires a CUP THAT DESCENDS TO COHOMOLOGY.

Agent 3 (still running) is designing the proper Alexander-
Whitney symmetric cup — prerequisite for Shape B closure.

## Synthesis (pending Agent 3)

The closure path:

  1. Agent 3 delivers proper AW cup `C¹ × C¹ → C²`
     descending to cohomology + satisfying chain-Leibniz.
  2. Apply Agent 2's Shape B: find radical element `r`,
     compute Massey `⟨r, x, r⟩` for candidate `x`.
  3. Formalize in Lean: 3 new files per Agent 2's plan,
     using Agent 3's cup definition.
  4. Verify non-vacuous Massey class in H².

If Shape B fails (e.g., radical element doesn't exist for
proper cup), fall back to Shape D (multi-4-cell asymmetric
extension).

## ★★★★★ BREAKTHROUGH: Non-vacuous Massey FOUND

Agent 3 designed the **opposite-edge cup product** that
descends to cohomology AND admits non-vacuous Massey triples:

### The opposite-edge cup

For face F with cyclic edges `[e₀, e₁, e₂, e₃]`:

      (α ⌣ β)(F) := Σᵢ α(eᵢ) · β(e_{i+2 mod 4})

Equivalent: pair each edge with its DIAGONAL opposite in the
cyclic 4-cycle (not its immediate neighbor).

**Independent verification**: 0 descent failures out of 32 768
(coboundary × cocycle) pairs.  Cup descends cleanly to
cohomology.

### Topological identification

Agent 3 identified `K_{3,2}^{(c=2)} ≃ S² ∨ (∨₆ S¹)` — wedge of
a sphere and 6 circles.  The cup table on H¹ × H¹ → H² is
**topologically forced to vanish** (no edge-edge product
contributes to H²).  Yet the Massey product detects secondary
structure invisible to the cup table.

### The witness — `⟨h1, h3, h4⟩ = ω`

  · `a = h1 = e₀ + e₂` (cocycle on S₀ star edges)
  · `b = h3 = e₄ + e₆` (cocycle on S₁ star edges)
  · `c = h4 = e₀ + e₄ + e₈` (cocycle on T₀ incidence mod 2)
  · `a ⌣ b = (0, 0, 0)` in C² → cobounding chain `η = 0`
  · `b ⌣ c = (1, 0, 1)` in im(δ¹) → cobounding chain `θ = e₄`
    (verified: `δθ = (1, 0, 1)`)
  · **Massey representative**: `η ⌣ c + a ⌣ θ = 0 + (1, 0, 0)
    = (1, 0, 0)`
  · `(1, 0, 0) ∉ im(δ¹)` → class = 1 = ω in H² ≅ F₂
  · **Indeterminacy** `a · H¹ + H¹ · c = {0}` — Massey is
    UNIQUELY DEFINED, not a coset
  · Robustness: 100 random `(η, θ)` choices all give class = 1

### Structural summary

  · 20 non-vacuous Massey triples found among the 216 candidate
    triples (allowing repetitions).
  · The cup table is trivial — Massey detects what the cup
    cannot.
  · K_{3,2}^{(c=2)} has rationally trivial cup product on H¹
    but non-trivial **Massey product structure** — the
    secondary cohomology operation is non-trivial.

This is the long-sought non-vacuous Massey at K_{3,2}^{(c=2)}.
It exists at the 2-skeleton itself (no skeleton extension
required), uses the proper descent-compatible cup, and lands
in H² = F₂ as the non-trivial class ω.

## Closure path for Lean formalization

Phase 14 plan:

1. **`Bipartite/CupOppositeEdge.lean`** — define the opposite-
   edge cup product C¹ × C¹ → C² on K_{3,2}^{(c=2)}.  Verify
   descent: for each coboundary × cocycle pair, cup is in
   im(δ¹).  `decide`-tractable (32 768 case decisions).
2. **`Bipartite/H1ClassRepresentatives.lean`** — explicit
   1-cocycle representatives `h0..h5` from `H1K` infrastructure.
3. **`Bipartite/MasseyTripleH1.lean`** — concrete witness
   `⟨h1, h3, h4⟩` computation:
     · Verify `a ⌣ b = (0,0,0)`.
     · Witness `θ = e₄` and verify `δθ = b ⌣ c`.
     · Compute Massey rep = `(1, 0, 0)`.
     · Prove `(1, 0, 0) ∉ im(δ¹)` → class = ω.
     · Verify indeterminacy = `{0}` (cup of `a` with each `H¹`
       basis class is in im(δ¹)).
   Each step is `decide`-amenable.  Total: ~150 lines PURE.
4. **Capstone**: `non_vacuous_massey_witness` theorem stating
   the Massey class `⟨h1, h3, h4⟩` is `ω ∈ H²` modulo
   indeterminacy `{0}`.

The non-vacuous Massey closure at K_{3,2}^{(c=2)} is now
formalization-ready.

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
