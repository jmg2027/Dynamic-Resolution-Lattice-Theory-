# G123 — Geometrization open follow-ups registry

**Date**: 2026-05-22
**Branch**: `claude/g121-open-followup-BCOp3`
**Purpose**: single authoritative list of every actionable item left
open by G121 (the Geometrization R1 close + R1+ partials).
Companion to `G107_action_items_registry.md` (G90-G106 items) — same
shape, narrower scope.

Sources:
  · `research-notes/G121_dim4_self_pointing_axis.md` §6 + §FW + R1+ tail
  · `theory/math/geometrization_conjecture.md` "Open frontier"
  · `lean/E213/Lib/Math/GeometrizationConjecture/INDEX.md` marathon table
  · `HANDOFF.md` 2026-05-22 closure log

R1 itself is **CLOSED** at 149 PURE / 0 DIRTY across 25 steps; this
registry covers only what remains after promotion of R1 to
`theory/math/geometrization_conjecture.md` and after the three
R1+ files (`Generalization`, `JsjDeep`, `MetricGeometries`) landed.

---

## §0.  Numbering note — G122 collision

G121's own `§FW` registry (step 25, commit `5d4137b0`) tagged its
four marathon candidates **G122 / G123 / G124 / G125**.  Between
G121's close and this registry, branch
`claude/lean4-ast-patterns-g1gWN` merged and claimed **G122** for
the Real213-p-adic campaign (per `HANDOFF.md` "Next campaign").
The G121-internal labels are therefore stale:

| G121 §FW label | G121-internal topic            | Post-renumber name used in this registry |
|---|---|---|
| ex-G122 | 4-mfd exotic enum via Sym(3) gauge | **FW-1**  (marathon, unnumbered until launch) |
| ex-G123 | JSJ deeper close (3-cell complex)  | **FW-2**  (partial via `JsjDeep.lean`) |
| ex-G124 | K_{NS,NT}^{(c)} chartBase ≥ 9      | **FW-3**  (partial via `Generalization.lean`) |
| ex-G125 | E³/H³/H²×ℝ direct realization      | **FW-4**  (partial via `MetricGeometries.lean`) |

`theory/math/geometrization_conjecture.md` already silently
relabeled these as "Real213-p-adic extensions A/B/C"; this file
makes the rename explicit.  When any of FW-1..FW-4 actually
launches as a marathon, it picks the next chronological G-number
at that time — **don't pre-allocate**.

---

## §1.  Open items — ordered by readiness

### FW-1 — 4-mfd exotic enumeration via Sym(3) gauge  [MARATHON, OPEN]

**Trigger**: user 2026-05-22 (G121 step 25): "4차원을 좌절할 게
아니라 가장 투명하게 잘 보여주는 거였던건데… 그 엑조틱 자체를
조사해봣으면 달랐을지두".

**Goal**: an explicit 213-native counting theorem for exotic smooth
structures on closed 4-manifolds, derived from K_{3,2}^{(c=2)} gauge
data (Sym(3) action, |Aut(K)| = 768, gluon-octet coker(ι*)).

**Scaffold already in place**:
  · `c3_chain_master` (`Physics/Symmetry/C3ChainCapstone.lean`) —
    Sym(3) gauge action + (F_2)^8 coker
  · `EightGeometries.all_eight_via_single_mobius_P` — single P,
    7 mod-k Lenses, 8 narratives
  · `Capstone.dim4_information_richness` — d=4 = unique two-branch
    dimension

**Missing**: a Lean-formalized exotic-count statement
`exoticCount4Mfd : Nat → Nat` (or analogous) with a structural
derivation from the Sym(3) gauge layer.  Standard math comparison:
Donaldson's instanton-moduli space.

**Effort**: marathon (likely 6-12 sessions, parallels FLUX-1 / COH
scale per `HANDOFF.md` open work §B).

**Falsifier potential**: HIGH.  An explicit exotic-count prediction
that disagrees with Donaldson invariants on a known 4-manifold
falsifies the Sym(3)-gauge ↔ exotic-smooth correspondence — i.e.,
falsifies M2/M3 together for the 4-mfd deployment.  Promotes G121
toward DRLT Validation Standard.

---

### FW-2 — JSJ deeper close (3-cell complex)  [PARTIAL]

**Current state**: `JsjDeep.lean` (~10 PURE) — χ-target scaffold
(`chi_closed_3mfd := 0`, `chi_K32_extended k j`, sphere Euler chain
∂Δⁿ for n=2..5).  Bipartite S/T cut as canonical decomposition
formalized.

**Missing**:
  · Full 3-cell complex `Filled.lean` extension (current Filled
    only handles 2-cells).
  · K_{3,2}^{(c=2)} ∪ k 2-cells ∪ j 3-cells → S³ realization
    (need k − j = 7).
  · JSJ-torus-cut lift from bipartite-graph cut to manifold-level
    cut (still narrative-only).

**Effort**: medium (3-5 sessions).

**Falsifier potential**: LOW (structural pillar deepening, not a
measurable prediction).

---

### FW-3 — K_{NS,NT}^{(c)} higher-chartBase generalization  [PARTIAL]

**Current state**: `Generalization.lean` (~7 PURE) — chartBase
∈ {4..8} extended.  Key theorem: **K_{3,2}^{(c=2)} unique across
chartBase ∈ {4..8}** under `passesCohomologyDepthFilter`.

**Missing**:
  · chartBase ≥ 9 exhaustive depth-filter verification.
  · `passesCohomologyDepthFilter` parameterized over (n, m, c) at
    arbitrary bound — abstract filter machinery, replacing the
    per-chartBase exhaustive lists.
  · Asymptotic statement: K_{3,2}^{(c=2)} is the **unique** match
    across **all** chartBase ≥ 4 (not just 4..8).

**Effort**: medium (3-5 sessions, mostly mechanical via abstraction
patterns from `META_SCAN_ARCHETYPES`).

**Falsifier potential**: MEDIUM.  A chartBase ≥ 9 deployment that
passes the depth filter would falsify K_{3,2}^{(c=2)} uniqueness —
re-opens M1.

---

### FW-4 — E³/H³/H²×ℝ direct realization (metric geometries)  [PARTIAL]

**Current state**: `MetricGeometries.lean` (~11 PURE) — Möbius P
mod-k Lens family extended to F_2 / F_3 / F_5 / F_7 / F_11.  Per
the table in `INDEX.md`: F_2 → E³ candidate (flat), F_3 → H²×ℝ
candidate, F_7 → H³ candidate, F_11 → split-geometry candidate.

**Missing**:
  · Metric-formalization for flat (E³): currently only "irreducible
    over F_2" narrative.  Need a 213-native flat-metric type.
  · Hyperbolic (H², H³, H²×ℝ): narrative-only via P trace > 2.
    Need 213-native hyperbolic-metric type.
  · The mod-k Lens narratives are **candidates**, not derivations.
    Promotion requires a uniqueness theorem of the form "modulus k
    forces geometry G_k" for each k ∈ {2, 3, 7, 11}.

**Effort**: marathon (likely 5-8 sessions; depends on whether
ε-Lens infrastructure from `Topology/Continuity` + `Analysis/
BracketCauchyModulus` extends to flat/hyperbolic metrics).

**Falsifier potential**: MEDIUM.  Concrete mod-k Lens → geometry
assignment is testable against Thurston's classification.

---

## §2.  R1 knots — residual

From G121 §6, the knots survive R1 close in reduced form:

| Knot | R1 status | Residual open part |
|---|---|---|
| **M1** | TWO-ROUTE CLOSE (atomicity + Möbius, K_{3,2}^{(c=2)}) | Generalize M1-close to all chartBase ≥ 9 → folded into FW-3 |
| **M2** | PARTIAL CLOSE (V32Betti + axiom-level shadow, K_{3,2}^{(c=2)}) | Abstract `KChartLens` type with `chartVisibleAxes = dim im δ⁰` for any K_{NS,NT}^{(c)} — folded into FW-3 |
| **M3** | downstream (physics interpretation) | NT-axis split into time + self-pointing.  **Re-activate only when physics push reactivates**; not a Lean-formalizable item in current state.  See G121 §6.3. |
| **M4** | doc-level (stereotype-matching warnings) | Maintain "this is not Kaluza-Klein" anchor in any expansion; cite G121 §6.4.  Permanent doc-hygiene, no marathon. |

M1 and M2 are fully subsumed by FW-3 (chartBase generalization).
M3 is dormant.  M4 is a permanent style constraint, not a task.

---

## §3.  Narrative-deepening items (I-series from G121 R1+)

Below-FW-priority refinements surfaced in G121 R1+ tail
("next-session entry point" §3).  None are blocking; all could
be picked up opportunistically:

| ID | Topic | Effort |
|---|---|---|
| **I-1** | 8-geometry ↔ Sym(3) basis-correspondence (explicit basis for 2·trivial ⊕ 3·standard ↔ 3 iso + 5 aniso assignment) | small (1-2 sessions) |
| **I-2** | Filled.lean → 3-cell complex extension | subsumed by FW-2 |
| **I-3** | Ricci flow ↔ chart-Lens averaging (full ε-Lens treatment) | small-medium (2 sessions) |
| **I-4** | Poincaré ↔ trivial-loop-residue (refine via `V32Betti.b0_eq_1` connectedness work) | small (1 session) |

I-2 is duplicate of FW-2.  I-1 / I-3 / I-4 are independent micro-marathons.

---

## §4.  Cross-frame deepening (G121 R1+ §C5)

The structural mapping `Geometrization 8 + gluon octet +
K_{3,2}^{(c=2)} cohomology + Möbius P pentagonal closure → one
algebraic spine` (theory chapter §"Cross-frame connections")
already cites four chapters.  Open: a single capstone theorem
bundling these four sources into a unified statement.

| ID | Statement (informal) | Effort | Status |
|---|---|---|---|
| **X-1** | Capstone theorem: "Sym(3) decomposition of 8-element substrate is invariant across {Geometrization classification, gluon octet, HC_K32 cohomology, Möbius P mod-5 closure}" | small (1 session, mostly bundling existing PURE results) | **CLOSED** ✅ `G121_X1_sym3_cross_frame_capstone` in `lean/E213/Lib/Math/GeometrizationConjecture/CrossFrame.lean` (2026-05-22) |

X-1 is a meta-capstone — adds no new mathematics, just records the
4-way convergence as a single citable theorem.

---

## §5.  What this registry is NOT

  · **Not a marathon launch**.  FW-1 and FW-4 are marathon-shaped
    but launching either requires explicit user direction (matches
    `marathon-start` skill convention).
  · **Not a re-opening of R1**.  R1 is closed and promoted; this
    registry catalogs *follow-ups*, not corrections.
  · **Not a precision-theorem candidate**.  Per G121 §8 + theory
    chapter "Below DRLT Validation Standard" — none of FW-1..FW-4
    is a precision theorem yet.  FW-1 has the strongest path
    toward falsifier-form (Donaldson-comparable count).
  · **Not a renumbering proposal**.  The G121-internal G122-G125
    labels are kept as historical references in §0; new marathon
    numbers are picked at launch time only.

---

## §6.  Recommended ordering (when work resumes)

Conditional on user direction; default sequencing:

1. ~~**X-1** (1 session, easy capstone)~~ — **DONE** 2026-05-22.
2. **I-1** + **I-4** (2-3 sessions combined) — small Lean
   additions, narrative-deepening, no new infrastructure.
3. **FW-3** (medium marathon) — abstract filter machinery is
   reusable and folds M1/M2 residual into one place.
4. **FW-2** (medium marathon) — Filled.lean 3-cell extension is
   prerequisite to FW-4's hyperbolic metric work anyway.
5. **FW-4** (marathon) — direct metric realization closes the
   metric-geometries side of EightGeometries pillar.
6. **FW-1** (marathon) — exotic enumeration via Sym(3) gauge.
   **Highest falsifier potential**; biggest single advance toward
   DRLT Validation Standard for G121.

I-3 is parallel to anything; can interleave.

---

## §7.  Cross-references

### Closed sources
  · `research-notes/G121_dim4_self_pointing_axis.md` — full G121 narrative
  · `theory/math/geometrization_conjecture.md` — promoted R1 chapter
  · `lean/E213/Lib/Math/GeometrizationConjecture/` — Lean sub-tree (12 files + INDEX)

### Registry kin
  · `research-notes/G107_action_items_registry.md` — G90-G106 items, same shape
  · `HANDOFF.md` open work §B — G107 still-open subset

### Anchor docs
  · `theory/PROMOTION_CRITERIA.md` — when does an FW item promote?
  · `seed/AXIOM/08_falsifiability.md` §8 — Validation Standard
  · `seed/META_SCAN_ARCHETYPES.md` — abstraction patterns for FW-3
