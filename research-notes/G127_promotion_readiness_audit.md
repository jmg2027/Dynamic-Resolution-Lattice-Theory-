# G127 — Promotion-readiness audit (Geometrization-family marathons)

**Date**: 2026-05-22
**Status**: audit / tracking document
**Purpose**: Per `theory/PROMOTION_CRITERIA.md`, a sub-tree promotes
from `research-notes/` to `theory/` chapter only when **all** Hard
criteria (H1-H4) and Soft criteria (S1-S3) are met.  Partial closes
fail S1 ("Categorical closure: core meanings all present").

This audit catalogs the partial-close G-marathons from the
Geometrization family and lists what blocks each from promotion.
Closing these blockers is THE work that elevates partial closes to
promotable chapters.

## Why this catalog exists (not a "new G-marathon")

The follow-up implementation work below was initially mis-labeled as
candidate new G-numbers (G127..G136).  Reclassified: these are
**promotion-blockers within existing G-marathons**, not new research
directions.  Tracking them per-G-marathon avoids G-number inflation
while keeping the work visible.

---

## §1.  G123 (Geometrization follow-up registry) — promotion status

**Current state**: 10 marathon items closed at various depths in
`lean/E213/Lib/Math/GeometrizationConjecture/` (~200+ PURE) +
`lean/E213/Lib/Math/Cohomology/Bipartite/Filled3Cell.lean` +
`lean/E213/Lib/Math/Geometry/MetricTypes.lean` +
`lean/E213/Lib/Math/AkbulutCork/` (44 PURE).

**Target chapter**: `theory/math/geometrization_conjecture.md`
already exists with "Open frontier" section; needs upgrade to full
chapter when blockers close.

### G123 promotion blockers

| FW item | Promotion blocker | Lines of work est. |
|---|---|---|
| FW-2 (JSJ deeper) | Topological attaching-map types for `Cell3ComplexK32` (currently Euler-target arithmetic only); JSJ-torus-cut graph cut → manifold cut lift | ~80 PURE, 4-6 sessions |
| FW-4 (metric direct realization) | Actual 213-native flat / hyperbolic metric tensor types beyond `MetricSignature` discrete classifier | ~60 PURE, 3-5 sessions |
| I-3 (Ricci ε-Lens) | Perelman 𝓕 / 𝓦 monotone functional analogs in Nat-valued modulus form; currently `K32_ricci_modulus` is step-count only | ~50 PURE, 3-4 sessions |
| X-1 (cross-frame) | Formal functor between Geometrization layer and Hodge layer; currently statement-level cross-frame capstone only | ~30 PURE, 1-2 sessions |
| 8-geometries depth | Lie group infrastructure (SL(2,ℝ), Heisenberg nilpotent, ~SL₂(ℝ) universal cover); currently all narrative-only | ~100 PURE, 5-8 sessions |

**Total to promotion**: ~320 PURE, 16-25 sessions.

**Soft criteria audit**:
- S1 Categorical closure: ✗ (FW-2/FW-4/I-3/8-geo all narrative-deep but implementation-shallow)
- S2 Downstream-ready: partial (`Capstone.dim4_information_richness` etc. cited by AkbulutCork; API exists)
- S3 Research-note closure: ✗ (G121, G123 still active top-level)

---

## §2.  G124 (V32Betti parametric) — promotion status

**Current state**: 3 files, 36 PURE in `Cohomology/Bipartite/Parametric/`.
`decide`-based verification across G121-relevant deployments.

**Target chapter**: `theory/math/cohomology/bipartite_parametric.md`
(would be new chapter).

### G124 promotion blockers

| Item | Blocker | Lines of work est. |
|---|---|---|
| Universal Nat-quantified theorem | `∀ NS NT c, 1 ≤ NS → 1 ≤ NT → 1 ≤ c → kerSizeDelta0Direct NS NT c = 2` requires graph-walk connectedness induction — no infrastructure for graph walks yet | ~80 PURE, 4-6 sessions, new `GraphWalk/` infra |
| Higher chartBase b_1 formula coverage | Currently verified at G121-deployment family only; extend to chartBase ≥ 9 | ~20 PURE, 1-2 sessions |

**Total to promotion**: ~100 PURE, 5-8 sessions.

**Soft criteria audit**:
- S1: ✗ (representative range ≠ universal — categorical closure fails)
- S2: ✓ (Bridge to KChartLensAbstract exists)
- S3: ✗ (G124 research note still active)

---

## §3.  G125 (BracketCauchy ↔ IsRicciModulus) — promotion status

**Current state**: `Topology/ModulusStructure.lean` (12 PURE).

**Target chapter**: probably *absorbed* into
`theory/math/analysis/cauchy.md` or similar (small enough not to
need a standalone chapter).

### G125 promotion blockers

| Item | Blocker | Lines of work est. |
|---|---|---|
| Option B (category-theoretic) | Full category-theoretic functor between `IsContinuousModulus` and `IsRicciModulus` — requires 213-native category theory infra (no `Cat` / `Functor` types yet) | ~200+ PURE, separate marathon |

Option A is **complete** — the 3-way framework is closed.  Option B
is a deeper extension that may not be necessary for promotion (the
typeclass framework suffices for S1 categorical closure of the
shared modulus pattern).

**Recommended path**: declare G125 promotable at Option A close.
Option B becomes a *separate* future marathon if/when category
theory infra is needed for other reasons.

**Soft criteria audit**:
- S1: ✓ (3-way framework captures the shared pattern; nothing
  material missing for the modulus-bridge use case)
- S2: ✓ (Bridge usable from any Nat → Nat modulus source)
- S3: ✗ (G125 research note still active; needs absorption)

**G125 is the closest to promotion** — only S3 (absorb research
note into target chapter) blocks.

---

## §4.  G126 (Akbulut cork) — promotion status

**Current state**: 4 files, 44 PURE in `AkbulutCork/`.  Signed
cork-twist count `+4` established.

**Target chapter**: `theory/math/exotic_4mfd_cork.md` (new).

### G126 promotion blockers

| Item | Blocker | Lines of work est. |
|---|---|---|
| Higher cohomology cork-twist (b_2, b_3) | `Filled3Cell.lean` cell-complex extension to b_2 / b_3 calculations; M_S01 action on higher cohomology classes; currently only H¹ level | ~70 PURE, 3-5 sessions (depends on G123 FW-2 deepening) |
| Multi-cork structures | Cork-of-cork iterated Z/2 actions on K-deployment; higher-order signed counts | ~40 PURE, 2-3 sessions |
| Specific 4-mfd Donaldson comparison | OPEN by design (external interface, 213/standard-math boundary) — NOT a promotion blocker for the 213-internal cork-theorem chapter | — |

**Total to promotion**: ~110 PURE, 5-8 sessions.

**Soft criteria audit**:
- S1: ✗ (cork-twist effect on higher cohomology missing — categorical
  closure incomplete for "the cork-twist theory of K_{3,2}^{(c=2)}")
- S2: ✓ (Bridge to existing GeometrizationConjecture infra)
- S3: ✗ (G126 research note active)

---

## §5.  G122 (Real213-p-adic) — promotion status

**Current state**: 4 files, 42 PURE in `Padic/`.  Phases 1, 2, 3, 6
partial.

**Target chapter**: `theory/math/padic/real213_padic.md` (new).

### G122 promotion blockers

| Item | Blocker | Lines of work est. |
|---|---|---|
| Phase 2 multiplication | `Zp.mul` digit convolution; uses G119 `mul_mod_pure` | ~30 PURE, 2 sessions |
| Phase 4 Hensel lifting | p-adic inverse via `modInverseFromBezout` (G119 Bezout); existence of x⁻¹ in ℤ_p for x coprime to p | ~60 PURE, 3-4 sessions |
| Phase 5 ℚ_p localisation | Ratio types for two `ZpSeq` representatives; equivalence classes | ~50 PURE, 2-3 sessions |
| Reverse `eq_mod_pn ↔ trunc-equality` | Unique base-p representation argument; currently only forward direction | ~30 PURE, 1-2 sessions |
| Substantive Phase 6 DRLT integration | Lift DRLT precision-bounded results (α_em, m_μ/m_e) to 5-adic analogues | ~50 PURE, 3-5 sessions |

**Total to promotion**: ~220 PURE, 11-16 sessions.

**Soft criteria audit**:
- S1: ✗ (Phases 4, 5 completely absent; Phase 2 incomplete)
- S2: partial (Foundation usable; arithmetic limited to add/neg)
- S3: ✗ (G122 research direction still active)

---

## §6.  Recommended ordering for promotion sweep

If the goal is **promotion of as many marathons as possible**,
optimal ordering:

1. **G125 → promote at Option A close** (S3 absorption only blocker)
   — 1 session: write `theory/math/analysis/modulus_structures.md`
   absorbing the G125 note.

2. **G124 → promote after universal Nat-theorem** (graph-walk
   infra is single new prereq)
   — 5-8 sessions: build `GraphWalk/` + Nat-universal close +
   chapter write.

3. **G126 → promote after b_2/b_3 cork extension** (G123 FW-2
   deepening is prereq)
   — 5-8 sessions: Filled3Cell extension + cork higher-cohomology +
   chapter write.

4. **G123 → promote LAST** (depends on G126 substantive close +
   FW-2/FW-4/I-3/8-geo deepenings)
   — 16-25 sessions: full sweep + chapter write.

5. **G122 → independent** (own track, not blocked by Geometrization
   family)
   — 11-16 sessions: Phases 2-mul, 4, 5 + substantive 6 + chapter.

**Grand total**: ~38-58 sessions for full promotion of all 5
marathons.  G125 is the cheapest first win.

---

## §7.  Decision points before sweeping

  · Is the "graph-walk connectedness" infrastructure for G124
    Nat-universal worth building as a standalone marathon?  Once
    built, it enables G124 promotion + future K-deployment proofs.
  · Should G123 FW-2 deepening (attaching maps) be its own
    sub-tree, or merged into `Cohomology/Bipartite/`?
  · For G126 multi-cork structures: do iterated cork-twists give
    a meaningful 213-native invariant beyond the signed count +4?

These are doctrinal decisions to make before launching the sweep.
