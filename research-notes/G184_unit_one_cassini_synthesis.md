# G184 — the unit `1`, the Cassini multiplier, and the depth-0 floor (frozen=dynamic synthesis)

**Date**: 2026-06-02.  **Status**: closed ∅-axiom results + honest non-bridges.  **Method**:
three parallel agents (unit-1 connection map + unit-unification conjectures + cross-frame
breakthrough hunt), synthesized.  **Thread**: the residue / frozen=dynamic / **unit `1`** axis,
continuing `PhiFrozenDynamic` (§5.7 frozen=dynamic φ).

## The thread

`frozen_eq_dynamic_phi` left a **residue unit `1`** between frozen φ (algebraic fixed point) and
dynamic φ (Pell limit): the convergent stays exactly `1` off the fixed-point relation and never
reaches it.  This `1` recurs across the repo; the agents mapped which appearances are *literally*
the same object vs merely both `1`, and the gaps closable.

## Proved this session (∅-axiom)

### C1 — the orbit determinant `det Pⁿ` **is** the atomic glue `NS − NT`  (`Cauchy/PhiResidueGlue`, 3 PURE)
**`orbit_det_is_glue`** (the load-bearing structural identity): the *actual matrix-power*
determinant `det Pⁿ = Q00 n · Q11 n − Q01 n²` (`PnFibonacciUniversal.det_pn_universal`, `= 1`)
**equals** `NS − NT` — `Q00 n · Q11 n = Q01 n² + (NS − NT)`.  A genuine arrow (shared matrix `P`,
the convergent orbit's generator), not a coincidence of `1`s.  `phi_residue_is_glue`: the
analysis-side reading — the φ-convergent cross-determinant `W n` reads the same constant
`NS − NT`.  `residue_unit_three_scales` bundles algebra (`det Pⁿ`), analysis (`W`), atomicity
(`NS − NT = 1`).  **(Adversarial-corrected: the original prose claimed `W n` was "literally
`det Pⁿ`" with no proof — that was the both-equal-1 trap; replaced by the real
`orbit_det_is_glue` via `det_pn_universal`.)**

### C2 — the parametric Cassini multiplier law (THE breakthrough)  (`CassiniUnimodular` §5, +4 PURE)
`det_step`: for **any** 2nd-order `Int` recurrence `s(n+2) = p·s(n+1) − q·s(n)`, the Cassini
determinant multiplies by the shift determinant `q` each step — `det s (n+1) = q · det s n` (one
`ring_intZ`; **no `q²=1` needed**).  `det_closed`: `det s n = qⁿ · det s 0` (`qpow`,
propext-free, since Mathlib-free Lean lacks `pow_succ`/`pow_zero` for `Int`).
`cassini_law_one_at_two_multipliers`: `det_golden` (`q=1`, conserved `=5`) and the period-2 orbit
(`q=−1`, alternating `±1`) are **one law at two multipliers** — *both branches enacted as
`det_step` instances* (`det_step 3 1` and `det_step 0 (-1)`; adversarial-corrected — the period-2
side originally reused the old standalone lemma, making the unification cosmetic).

### C7 — `q=1` (`SL₂`) ⟹ depth-0 Cassini floor  (`Cauchy/CassiniDepthFloor`, 3 PURE)
`cassini_conserved_depth0`: a `q=1` orbit (`SL₂` shift) has a *constant* Cassini, hence
`polyDepthZ 0 (det s)` — the `SL₂` orbit is the divergence-ladder **floor**.  `sl2_cassini_floor`
bundles the *sufficiency* + the golden instance (`det L = d = 5`).  Generalizes
`DepthResidueFloor.floor_polyDepth0` (the φ/`W` instance) to the law behind it.
**`conserved_never_degenerate`** (the residue, generalized): a `q=1` orbit with `det s 0 ≠ 0`
has `det s n ≠ 0` at every layer — it *never* reaches the degenerate (frozen) relation
`s(n)·s(n+2) = s(n+1)²`.  The conserved Cassini unit **is** the residue between dynamic and
frozen, for *every* `SL₂` orbit — generalising `FibCassiniNat.convergent_never_frozen` (the φ
instance) and `golden_never_degenerate` (`det L = 5 ≠ 0`).  So the multiplier `q=1` gives *both*
faces: the depth-0 floor *and* the never-reached residue.
**(Adversarial-corrected scope:** one-directional `q=1 ⟹ depth 0`, **not** a biconditional — the
converse is false for degenerate `det s 0 = 0`; only `q=1`/`SL₂` is covered, **not** all
unimodular `|q|=1` (`q=−1` period-2 alternates); and "the ζ-ladder is the degree of departure
from this floor" is a **conjectural reading, not formalized**.)

## The proved unit-`1` connection map (agent 1)

Literally the same object (existing theorems):
  - depth descent unit = ascent unit (`part_depth_succ_le`, `ascent_adds_unit`).
  - Raw peel unit = tower overflow unit (`ReentryUnit.reentry_unit_across_scales`).
  - Möbius `det = NS − NT` (`mobius_det_eq_ns_minus_nt`).
  - Cassini floor = `det P = 1` (`DepthFloorDetOne.depth_floor_is_det_one`).
  - **NEW (C1)**: φ-convergent cross-determinant `W n = NS − NT = det P` — chains analysis to
    atomicity/algebra.

## Honest non-bridges — record and STOP re-fighting

  - **φ-Cassini `+1` vs Raw depth-descent `+1`** — both `Nat` successors, but NO theorem links
    them and G177 already demoted this to "thematic grouping" (different objects: a Cassini
    constraint on Fibonacci pairs vs a structural peel on `Raw`).  Bundling them (`floor_vs_escape`
    capstone) would be a content-free naming theorem — the "everything equals 1" failure mode.
    **Avoid.**  The honest cross-scale unit is `reentry_unit_across_scales` (converge=escape) and
    C1 (`W = NS−NT`), not a φ-defect↔depth identity.
  - **Cohomology cup-image "residual"** (`V33EnrichedParametricDualSpan.psi_residual`) — the
    residual *closes* (`parametric_dual_span` says residual ∈ cup-image+coboundary), the
    **opposite** verdict to the residue (which never closes).  Calling it a residue-mirror is
    stereotype-matching.  **Not a bridge.**
  - **φ-Cassini "never frozen" vs Cantor diagonal escape** — same *shape* (approaches, never
    encloses) but **different engine** (unimodular Cassini `±1` vs `cantor_general` diagonal).
    `the_form_of_the_residue.md` already flags forcing a common map as a category error.  The
    honest unity is the shared `Nat` unit `1`, not a shared theorem.

## Cross-frame findings (agent 3) — deepest theme + future targets

  - **CP-4 (the load-bearing contrast)**: `P` as self-form fixed point
    (`CharPolySelf.p_self_reference_master`, `MobiusSelfForm`) is the **closing** self-reference —
    the *complement* of the residue (which never closes, `object1_not_surjective`).  "Two
    distinct closures meeting" (`G152`, `two_closures`): Lambek fixed-point vs well-founded floor.
    The residue axis has a *closing twin*.
  - **B-3 (future, hard)**: promote `SelfReferenceThreeOutcomes` from a conjunction of three
    unrelated objects to a **trichotomy indexed by image-totality** — P-description closes (image
    total → isolated fixed point), residue-cover escapes (image misses surplus → no fixed point),
    oscillation the boundary (involution, period-2, no fixed point but bounded).  The breakthrough
    IS finding the common ambient self-map type the docstrings currently say doesn't exist;
    absent it, this stays a §5.2 reading, not Lean.
  - **B-2 (high risk)**: connect geometrization `Ansatz.selfPointingAxes = 1` (`d_M = 5 − 1 = 4`)
    to a chart-level `cantor_general` non-surjectivity — genuine only if the chart self-map is
    actually constructed; otherwise analogy.

## Provenance

Three agents, 2026-06-02.  Anchors: `Real213/PhiFrozenDynamic`, `Cauchy/{PhiResidueGlue,
DepthFloorDetOne, DepthResidueFloor, CassiniDepthFloor, ReentryUnit}`, `CassiniUnimodular`,
`Mobius213OneAsGlue`, `Mobius213/Px/{CharPolySelf,MobiusSelfForm}`, `research-notes/G177`,
`catalogs/cross-domain-identifications.md` CDI-9.

## Bridge to the orbit-dimension ladder (G183_above_the_polynomials)

`cassini_is_polynomial` (`CassiniDepthFloor §3`): via `DepthCharacterization.finite_depthZ_iff`
(finite divergence depth ⟺ polynomial), the Cassini of an SL₂ (`q=1`) orbit is a **degree-0
polynomial** — it lands on the *bottom* rung of the divergence-depth ladder.  But the orbit `s`
itself (Fibonacci/Lucas, C-finite) is *above* the polynomials (depth `∞`, grows like `φⁿ`).  So
the **Cassini quadratic map collapses a depth-`∞` C-finite orbit to a depth-`0` polynomial** — a
depth-collapsing invariant linking the unit-`1`/Cassini arc to the concurrent orbit-dimension
ladder.  (The conserved Cassini unit is the bottom-rung shadow of the above-polynomial orbit.)

## CP-4 realized concretely: P closes, P's orbit never closes (det = 1 the hinge)

The cross-frame agent's deepest theme — the **closing / non-closing duality** (P's self-form is
the residue's *closing* twin) — is now concretely realizable through `P`, with the determinant
unit `q = 1` as the hinge.  Both faces are theorems (about `P` and about `P`'s orbit):

  - **closing** — `MobiusSelfForm.p_unique_sl2_trace3` / `p_self_reference_master`: `P` is the
    *unique* positive `SL₂` matrix with trace `NS = 3` and **det `= 1`** — an isolated, closing
    self-form fixed point;
  - **non-closing** — `CassiniDepthFloor.conserved_never_degenerate`: the orbit `P` generates
    (`q = 1`) keeps Cassini `= det s 0 ≠ 0` forever, so it *never* reaches its frozen fixed point.

The hinge is `det P = NS − NT = q = 1`: the *same* unimodular unit that **pins** `P` as a closed
self-form (the det-1 constraint in `p_unique`) is what makes `P`'s **orbit** non-degenerate and
never-closing (the `q=1` multiplier in `det_step`).  Honest scope: this is a *reading* linking two
genuine theorems about two aspects of `P` (matrix vs orbit) — NOT a forced single-ambient
trichotomy (B-3 remains open: that needs a common self-map type the docstrings say doesn't exist).
The concrete realization through `P` is the honest, non-forced form of CP-4.

## 2-1-3 as orbit residue-generation (Mingu Jeong's orbit reading, 2026-06-02)

> "213을 orbit 관점에서 보면 2개가 원을 그리면서 궤도를 계속 도는게 잔여 생성이라는 말인가봐
> 그 생성된 잔여까지를 각 층에서 보면 3개가 보인다는 말인가봐."

`orbit_two_generates_residue_seen_as_three` (`PhiResidueGlue`, PURE) is the formal witness, and
the reading is **structural, not a small-number coincidence**:

  - **2** = the orbit *order* = `NT`.  The atomic Möbius `P` (trace `NS = 3`, det `NS − NT = 1`)
    is `2×2`; its order-2 orbit is the pair `(s(n), s(n+1))` that keeps turning (the circle).
    `P`'s 2-dimensionality **is** `NT = 2` (`second_diff_closure`: the pair generates the next
    term, the orbit dimension `≤ 2`).
  - **the residue, generated** = the conserved Cassini unit, produced identically at every layer
    (`W m = W 0`, `det_step` at `q=1`): the orbit drawing the same residue each turn.
  - **3** = the Cassini/Wronskian *window* = order + 1 = `NT + 1 = NS`.  `det(n) = s(n)·s(n+2) −
    s(n+1)²` literally spans the 3 = `NS` consecutive terms `(n, n+1, n+2)` over the order-2
    orbit — and counting the generated residue (value `NS − NT`) with the pair gives `NS = NT + 1`.

So the **atomicity counting** `(NT, NS) = (2, 3)` and the **orbit geometry** `(order, window) =
(2, 3)` are *the same* `2-1-3`: the `1` (glue `= NS − NT = det P`) is not an independent third
atom but the residue the two-orbit generates, and `NS = NT + 1` is the layer-count *including* it.
Honest scope: this is the **atomic `P`-orbit** (where order `= NT`), the orbit forced by
atomicity — not a claim about arbitrary orbits.
