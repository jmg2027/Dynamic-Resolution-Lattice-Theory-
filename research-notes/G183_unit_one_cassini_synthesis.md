# G183 — the unit `1`, the Cassini multiplier, and the depth-0 floor (frozen=dynamic synthesis)

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

### C1 — the φ residue **is** the atomic glue `NS − NT = det P`  (`Cauchy/PhiResidueGlue`, 2 PURE)
`phi_residue_is_glue`: the φ-convergent cross-determinant `W n` (the residue between dynamic
convergent and frozen φ, `DepthFloorDetOne.W_eq_one`) **equals** `NS − NT`.
`residue_unit_three_scales`: the *same* unit `1` read at three scales — **analysis** (`W n`),
**atomicity** (`NS − NT`), **algebra** (`det P`) — chained by one theorem, not three coincident
`1`s.  Genuine: `W n` is literally `det Pⁿ = (det P)ⁿ = 1`.

### C2 — the parametric Cassini multiplier law (THE breakthrough)  (`CassiniUnimodular` §5, +4 PURE)
`det_step`: for **any** 2nd-order `Int` recurrence `s(n+2) = p·s(n+1) − q·s(n)`, the Cassini
determinant multiplies by the shift determinant `q` each step — `det s (n+1) = q · det s n` (one
`ring_intZ`; **no `q²=1` needed**).  `det_closed`: `det s n = qⁿ · det s 0` (`qpow`,
propext-free, since Mathlib-free Lean lacks `pow_succ`/`pow_zero` for `Int`).
`cassini_law_one_at_two_multipliers`: `det_golden` (`q=1`, conserved `=5`) and
`det_period2_alternates` (`q=−1`, alternating `±1`) are **one law at two multipliers** — subsumes
the golden/oscillation dichotomy under a single parametric theorem.

### C7 — unimodular (`q=1`) ⟺ depth-0 Cassini floor  (`Cauchy/CassiniDepthFloor`, 3 PURE)
`cassini_conserved_depth0`: a `q=1` orbit (`SL₂` shift) has a *constant* Cassini, hence
`polyDepthZ 0 (det s)` — the unimodular orbit is the divergence-ladder **floor**.
`unimodular_floor_capstone`: **depth 0 ⟺ conserved Cassini ⟺ unimodular self-reference**.  The
`DepthResidueFloor` ladder (e:1 → ζ(2):2 → ζ(3):3) is the *degree of departure* from this floor:
the floor is the rule that is its own fixed point (constant-coeff `q=1` Möbius shift); each
ζ-rung has `n`-dependent coefficients — polynomial drift from constant-Cassini self-reference.
Generalizes `DepthResidueFloor.floor_polyDepth0` (the φ/`W` instance) to the law behind it.

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
