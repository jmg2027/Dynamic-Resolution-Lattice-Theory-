# Frontier — closing the A6 core: discrete Ricci flow ladder

**Status**: OPEN marathon.  **Tier**: 1.  Anchor: A6 FLOW's *archetype* and *easy
cases* are closed (round sphere, Einstein trichotomy, gradient-flow skeleton),
but A6's **conquest core** — general Ricci flow / Perelman `𝓕/𝓦`-monotonicity —
is not.  This note is the durable agenda for closing it the 213-native way.

## Why the smooth core is walled

General-metric smooth Ricci flow needs Riemannian geometry (metric/connection/
curvature tensors), tensor calculus, and PDE a-priori estimates — none in
`lean/E213/`, Mathlib forbidden.  See `ricci_flow_smooth_core.md`.  That wall is
real; we do **not** climb it directly.

## The 213-native route: discrete Ricci flow

Ricci curvature has combinatorial incarnations needing **no smooth manifold** —
**Forman–Ricci** (cell-complex combinatorics) and **Ollivier–Ricci** (optimal
transport / coupling on the graph metric).  The repo lives in exactly this
discrete category (`K_{NS,NT}` graphs + cell complexes).  So the honest A6-core
closure is: build discrete Ricci curvature + discrete Ricci flow and drive a
genuine monotonicity / normalization theorem — all `∅`-axiom (curvature is a
combinatorial formula).

## Ladder (each rung a genuine ∅-axiom brick)

1. **Forman edge curvature** — ✅ DONE
   (`GeometrizationConjecture/DiscreteRicci.lean`, 6 PURE): `formanEdge du dv =
   4 − du − dv`; `K_{NS,NT}` uniform value `4 − NS − NT`; sign ↔ topology
   (`K_{1,1}` `+2`, `K_{1,3}` `0`, `K_{3,2}` `−1` ↔ `b₁` 0/0/8).
2. **Weighted Forman + a discrete Ricci-flow step** — NEXT.  Edge weights
   `w : edge → ℕ`/`ℤ`; flow step `w ↦ w − F·w` (or normalized).  Prove a
   per-step effect on a curvature monovariant.
3. **Monotonicity / convergence of discrete flow** — drive the flow to a
   constant-curvature (normalized) state via A6 FLOW (`flow_reaches`) on a
   curvature-spread monovariant.  *This is the discrete analogue of Perelman
   monotonicity and the real A6-core target.*
4. **Discrete Gauss–Bonnet / Bochner (CD(K,N))** — Bakry–Émery curvature-
   dimension on graphs; `Ric ≥ K` combinatorially; relate Σ curvature to Euler
   characteristic.  Connects curvature sign to `b₁` as a theorem, not a table.
5. **Ollivier–Ricci** (optimal-transport curvature) — heavier; needs a coupling
   / W₁ distance on the finite graph metric.  Later rung.

## Honest boundary

This closes A6's core **in the discrete (Forman/Ollivier) theory** — a genuine
parallel mathematics, not smooth Perelman.  The smooth core stays walled
(`ricci_flow_smooth_core.md`).  The claim to make: "A6 FLOW drives discrete
Ricci flow to its normalized fixed point" — not "A6 solves Poincaré."

## Next action

Rung 2: weighted Forman + flow step in `DiscreteRicci.lean`, then rung 3
(convergence via `flow_reaches`).
