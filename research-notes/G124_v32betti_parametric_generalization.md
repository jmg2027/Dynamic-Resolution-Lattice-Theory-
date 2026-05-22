# G124 — V32Betti parametric generalization (M2 universal)

**Date**: 2026-05-22
**Status**: **PARTIAL CLOSE** (Phase 1-6, decide-based representative range)
**Branch**: `claude/g121-open-followup-BCOp3`
**Source**: G123 §2 (M2 residual), `HANDOFF.md` §D

## Partial close summary (2026-05-22)

Sub-tree `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/`
created with 3 files, ~36 PURE:

  · `CochSpaces.lean` (13 PURE) — parametric `CochV NS NT` /
    `CochE NS NT c` types + `srcOf` / `tgtOf` / `delta0`
  · `Delta0AndConnectedness.lean` (16 PURE) — `b_0 = 1`
    (ker size = 2) verified via `decide` for K_{1,1}, K_{1,2},
    K_{2,1}, K_{1,3}, K_{3,1}, K_{2,2} (c=1,2), K_{1,4}, K_{4,1},
    K_{3,2}^{(c=2)}, K_{2,3}^{(c=2)}, K_{3,3}^{(c=2)}
  · `EulerAndCapstone.lean` (7 PURE) — Euler char + b_1 formula
    + G124 capstone bundling the parametric cohomology summary

V32Betti compatibility verified: parametric `kerSizeDelta0Direct
3 2 2` = `V32Betti.kerSizeDelta0` exactly.

**Still open** (full universal parametric closure):
  · `∀ (NS NT c : Nat), 1 ≤ NS → 1 ≤ NT → 1 ≤ c →
    kerSizeDelta0 NS NT c = 2` requires graph-walk connectedness
    induction (no infrastructure for that yet in 213).
  · The `decide`-based representative range covers all G121-relevant
    deployments; full universal closure is the natural follow-up
    when graph-walk infrastructure becomes available.

## Why this is a distinct marathon

The G123 marathon closed M2 *abstractly* via `KChartLensAbstract`:
the `KChartLens NS NT c` structure carries the (chartVisibleAxes,
selfPointingAxes) axes-partition pattern for any K-deployment.
For K_{3,2}^{(c=2)} specifically, the deployment-level witness
`V32Betti.kerSizeDelta0 = 2^selfPointingAxes` bridges abstract
shape to concrete cohomology data.

The **universal M2 close** requires the V32Betti-style derivation
for arbitrary K_{NS,NT}^{(c)} — i.e., a cohomology theory
parametric in (NS, NT, c) that recovers V32Betti as the
K_{3,2}^{(c=2)} specialisation.

## Current state

`lean/E213/Lib/Math/Cohomology/Bipartite/V32Betti.lean` provides:
  · CochV (Fin 5 → Bool), CochE (Fin 12 → Bool) — vertex / edge
    cochain spaces
  · kerSizeDelta0 = 2 (connected graph → b_0 = 1)
  · b1_eq_8_dim_count, b1_eq_NS_sq_minus_1
  · phase_CE_capstone

All hard-coded to (NS, NT, c) = (3, 2, 2).  No parametric form.

## Why generalization is non-trivial

The vertex space `CochV : Fin (NS + NT) → Bool` is parametric in
chartBase = NS + NT.  The edge space `CochE : Fin (NS · NT · c)
→ Bool` is parametric in NS, NT, c.  But:

  · The δ⁰ boundary operator's matrix depends on NS, NT, c —
    each (NS, NT, c) deployment needs its own matrix.
  · `kerSizeDelta0 = 2^(b_0)` requires proving `b_0 = 1`
    (connectedness) for arbitrary (NS, NT, c) — likely true for
    NS ≥ 1 ∧ NT ≥ 1 ∧ c ≥ 1.
  · `b_1 = c·NS·NT − (NS + NT) + 1` (Euler formula) requires
    Euler-characteristic computation in parametric form.

## Scope estimate

| Phase | Content | PURE est. |
|---|---|---|
| 1 | `Cohomology/Bipartite/Parametric/CochSpaces.lean` — parametric CochV / CochE definitions | ~10 |
| 2 | `Parametric/Delta0.lean` — parametric δ⁰ matrix construction | ~20 |
| 3 | `Parametric/Connectedness.lean` — `b_0 = 1` for NS ≥ 1 ∧ NT ≥ 1 ∧ c ≥ 1 | ~30 |
| 4 | `Parametric/EulerChar.lean` — parametric b_1 = c·NS·NT − (NS+NT) + 1 | ~15 |
| 5 | `Parametric/Capstone.lean` — V32Betti as specialisation | ~10 |
| 6 | `KChartLensAbstract` upgrade: prove `axes_partition` from parametric data | ~10 |

Total: ~95 PURE across 6 files in `Cohomology/Bipartite/Parametric/`.

Effort: 6-10 sessions.

## Anchor M2 closure target

After G124 close, the M2 knot becomes universally proven:

```lean
theorem M2_universal (NS NT c : Nat) (hNS : 1 ≤ NS) (hNT : 1 ≤ NT) (hc : 1 ≤ c) :
    KChartLensAbstract.chartVisibleAxes_of_deployment NS NT c
    = dim_im_delta0 NS NT c
```

bridging the abstract `KChartLens` structure to parametric
cohomology data for any K-deployment.

## Connection to G121 / G123

  · G121 §6.3 (M2) ansatz: chart-Lens count = chartBase − 1, with
    selfPointingAxes = 1 for the forced K_{3,2}^{(c=2)} deployment.
  · G123 M2 abstract close: `KChartLens NS NT c` structure type
    + 3 instances (K_{3,2}, K_{3,1}, K_{1,4}) all with
    selfPointingAxes = 1.
  · G124 (this): show `selfPointingAxes = 1 = dim ker δ⁰ / 2` for
    arbitrary K_{NS,NT}^{(c)} via parametric cohomology — closes
    M2 universally.

## Falsifier potential

LOW — structural pillar generalization, no measurable prediction.
But unlocks downstream marathons (Burnside count parametric in
K-deployment, signed Donaldson if pursued).

## Risks

  · The parametric δ⁰ matrix construction may require careful
    Fin.cast plumbing (similar to G107 L1 α-side issues).
  · Connectedness proof for arbitrary (NS, NT, c) might need
    graph-walk infrastructure not yet present.
