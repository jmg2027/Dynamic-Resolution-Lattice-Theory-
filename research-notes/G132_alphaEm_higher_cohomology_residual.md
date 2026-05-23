# G132 — 1/α_em sub-ppb precision via K_{3,2}^{(c=2)} higher cohomology

**Date**: 2026-05-22
**Status**: **Phase 1 anchor CLOSED** — Filled3CellCohomology shared
prereq established for three downstream marathons (this campaign,
G123 FW-2 JSJ-deepening, G126 Phase 7+ cork higher-cohomology)
**Branch suggestion**: post-G131 follow-up
**Source**: G131 Phase 4 open question (post-Gram residual 27 × 10⁻⁹
mathematical principle), per PROMOTION_CRITERIA discussion 2026-05-22.

## Phase 1 anchor (2026-05-22) — three-marathon shared prereq

`lean/E213/Lib/Math/Cohomology/Bipartite/Filled3CellCohomology.lean`
(17 PURE).  Establishes the attaching-map cohomology infrastructure
needed by all three downstream tracks.

**Headline structural finding**: the 3 simple 4-cycles of
K_{3,2}^{(c=2)} (Face 0 = {0,2,4,6}, Face 1 = {0,2,8,10}, Face 2 =
{4,6,8,10}) are **linearly DEPENDENT**:

  Face 0 ⊕ Face 1 ⊕ Face 2 = 0   (proven by case analysis)

Hence `rank δ¹ = 2`, not 3 — refining the naive `b_1 = 8 − k`
arithmetic of the existing `Filled.lean`:

  | k | naive b_1 | actual b_1 | actual b_2 |
  |---|-----------|------------|------------|
  | 0 | 8         | 8          | 0          |
  | 1 | 7         | 7          | 0          |
  | 2 | 6         | 6          | 0          |
  | 3 | **5**     | **6** ★    | **1** ★    |

At full simple-cycle filling (k = 3), **b_2 = 1**: the formal sum
Face 0 + Face 1 + Face 2 is a non-trivial 2-cocycle in F_2.  This
class is exactly the cohomological seed for the higher-cohomology
α_em residual candidate analyzed below.

**Provided structures**:
  · `face0_boundary, face1_boundary, face2_boundary` — boundary
    XOR operators per face
  · `face_dependence` (★★★★★) — algebraic identity
    Face 0 ⊕ Face 1 ⊕ Face 2 = 0 for any σ
  · `face2_redundant` (★★★★) — third constraint implied by first two
  · `cohomology_dims_at_full_simple` (★★★★★) — dim H¹ = 6, dim H² = 1
  · `Boundary3Cell j` stub — ready for j > 0 instances
  · `phase1_cohomology_anchor` (★★★★★★) — 6-conjunct capstone

Three downstream marathons can now build on this anchor:
  · **G132 Phase 2+** (this campaign): match `b_2 = 1` class to the
    27 × 10⁻⁹ post-Gram α_em residual via cup-ring trace
  · **G123 FW-2 Phase 7+**: lift the 2-cocycle to a real 3-mfd
    attaching-map structure (JSJ-deepening)
  · **G126 Phase 7+**: extend Akbulut cork-twist Z/2 action from
    H¹ to H² via the non-trivial 2-cocycle

## The residual

G131 closed `1/α_em` at the precision-theorem tier (0.2 ppb) via
the structural derivation
`1/α_em(structural) = X(NS,NT,c,d) − α²/d²`.

After this structural derivation, the residual to CODATA at e9 scale
is **exactly 27 × 10⁻⁹**:

```
alphaInv_structural_e9 = 137,035,999,111
observed_e9            = 137,035,999,084
                       ─────────────────
residual               =             27 × 10⁻⁹  ≈ 0.2 ppb
```

This is the open question of G131 Phase 4: **what mathematical
principle structurally derives this 27 × 10⁻⁹ residual?**

## Numerical scan

Candidates ordered by closeness:

| Structural form | Value at α ≈ 7.30 × 10⁻³ | vs 27 × 10⁻⁹ |
|---|---|---|
| α⁴ · NS² | 2.83 × 10⁻⁹ · 9 = 25.5 × 10⁻⁹ | −5.6% |
| α³ · NT/d² | 31 × 10⁻⁹ | +15% |
| α⁴ · 10 | 28.3 × 10⁻⁹ | +5% |
| α⁴ · E | α⁴·12 = 34 × 10⁻⁹ | +26% |
| α³/d² | 1.55 × 10⁻⁸ = 15.5 × 10⁻⁹ | −42% |
| α³ · NS/(d²·NT) | 23.3 × 10⁻⁹ | −14% |
| Pure α³ | 388 × 10⁻⁹ | ×14.4 too big |
| α_GUT² | 5.7 × 10⁻⁴ | ×20,000 too big |

**No single clean (structural integer) × (α-power) matches exactly**.
The closest is `NS² · α⁴ ≈ 25.5 × 10⁻⁹` (5.6% under).

Most likely, the residual is a sum of multiple structural contributions
across `α³`, `α⁴`, and `α_GUT²` orders.

## The five candidate principles

### Candidate 1: Dyson series beyond α²

Expanding `1/α(0)` as a perturbation series in `α`:
```
1/α(0) = X − α²/d² − C₃·α³ − C₄·α⁴ − ...
```
The Gram correction is the α² term.  G131 Phase 4 = derive `C₃, C₄,
…` from atomic principles.

### Candidate 2: Quartic self-consistency

Extending the cubic `25y³ + 1 = 25Xy²` to a quartic with a linear
correction `c_lin·y`:
```
25y³ + c_lin·y + 1 = 25Xy²
```
where `c_lin` is determined by some cohomological identity beyond
the cubic Newton truncation.

### Candidate 3: α_GUT² · structural divisor

`InvAlphaEMDecomp` captures `α_GUT/4` and `α_GUT/45`.  Next-order
`α_GUT²/D` would add a correction.  For 27 × 10⁻⁹: D ≈ 21,000 — no
clean atomic-factor decomposition visible.

### Candidate 4: Mixed α · α_GUT cross-coupling

Cross-terms `α^j · α_GUT^k` from the parallel-coupling structure
of 213 (`AlphaGUT`, `AlphaEM`, `TripleCoupling`).

### Candidate 5: **K_{3,2}^{(c=2)} higher cohomology contribution** ★

The current 5-layer base + Gram structural use only **H¹** of
`K_{3,2}^{(c=2)}` (cup-channels = 6, `b_1 = 8 = NS² − 1`).

K_{3,2}^{(c=2)} is a 1-skeleton, so `b_2 = b_3 = 0`.  But the
**Filled3Cell extension** (G123 FW-2, partially done) adds 2-cells
and 3-cells, yielding non-trivial `b_2, b_3`:
  · `Filled3Cell.Cell3ComplexK32` — k 2-cells + j 3-cells
  · `b_2 = k − j` (naive Betti under independent attaching)
  · `b_3 = j`

The 27 × 10⁻⁹ residual could be the **b_2 / b_3 cohomological
contribution** to the cup-ring trace.  Specifically: extending
`InvAlphaEMDecomp` from H¹-only to H¹ ⊕ H² ⊕ H³ would introduce
additional structural denominators that contribute at the α³, α⁴,
or α_GUT² order.

**This is the most 213-native candidate** — it connects directly
to existing G123 FW-2 infrastructure and gives a concrete cohomological
route to the residual.

## Connection to existing G-marathons

| G | Relevance |
|---|---|
| **G123 FW-2** (Filled3Cell scaffold, `Cohomology/Bipartite/Filled3Cell.lean`) | Parametric `Cell3ComplexK32` (k 2-cells + j 3-cells) + Euler-target + naive Betti.  Currently Euler-arithmetic only — needs cohomology-functor extension for G132 use. |
| **G126 Akbulut cork** | Phase 7+ candidate also depends on Filled3Cell b_2/b_3 extension.  G132 + G126 Phase 7+ share the same prereq. |
| **G131 GramStructural** | This research direction is G131's Phase 4 (post-Gram residual structural derivation).  Phase 4 is **not blocking** the 0.2 ppb precision-theorem tier; G132 would tighten precision below 0.2 ppb. |

## Phase plan (G132)

| Phase | Content | PURE est. | Sessions est. |
|---|---|---|---|
| 1 | Extend `Filled3Cell.lean` from Euler-arithmetic to full b_n functor (b_1 / b_2 / b_3) via attaching-map data | ~80 | 5-7 (depends on G123 FW-2 closure) |
| 2 | Extend `InvAlphaEMDecomp` to H² + H³ contributions: derive structural denominators that appear at b_2 / b_3 trace level | ~50 | 3-5 |
| 3 | Identify the α-order and atomic-factor coefficients of the H²/H³ contributions | ~40 | 3-4 |
| 4 | Numerical match: predicted residual = K · α^j (where K and j derive from H² / H³ structure) at 27 × 10⁻⁹ | ~30 | 2-3 |
| 5 | Capstone: `invAlphaEm_sub_ppb_precision_theorem` — full 1/α_em derivation including higher-cohomology correction, tighter than 0.2 ppb | ~20 | 1-2 |

**Total**: ~220 PURE, 14-21 sessions to full sub-ppb closure.

## Falsifier potential

**HIGH-PLUS**.  G131 already provides a 0.2 ppb falsifiability
contract.  G132 would tighten this to sub-ppb tier.  If the
structural form derived from H²/H³ cohomology disagrees with future
CODATA measurements below 27 × 10⁻⁹, the 213 framework is falsified
at the next-tier precision.

## Why NOT a marathon launch now

  · Depends on G123 FW-2 completion (currently `Filled3Cell.lean`
    is scaffold-level, not full attaching-map cohomology functor)
  · G131 is already at the 0.2 ppb tier — DRLT Validation Standard
    is satisfied without G132
  · G132 is "tightening precision" rather than "closing a gap" —
    nice-to-have, not blocking

## Recommended sequencing

1. First close **G123 FW-2 deepening** (full Filled3Cell with attaching
   maps + b_n functor) — needed prereq.
2. Then launch **G126 Phase 7+** (cork-twist on b_2/b_3) — uses the
   same prereq.
3. Finally G132 (1/α_em sub-ppb via higher cohomology) — uses both.

Or: launch G132 directly with the Filled3Cell scaffold as is, doing
necessary Filled3Cell extensions inline.

## Anchor file

The G131 Phase 4 question was discussed in detail in chat 2026-05-22:
see commit history for G131 phases 1-3 + 5 closure.  G131 research
note is being archived as part of `1/α_em` precision-theorem
promotion; the residual analysis above transfers here as the
forward-looking research direction.
