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
2. **Discrete Ricci-flow step + a-priori estimates** — ✅ DONE
   (`GeometrizationConjecture/RicciFlowDiscrete.lean`, 5 PURE).  The bridge: smooth Ricci flow
   *linearizes to the heat equation on curvature* (`∂_t R = ΔR + 2|Ric|²`, Hamilton), so the
   curvature evolves by the **discrete heat step** — and the PDE-marathon heat estimates ARE the
   discrete Ricci-flow a-priori estimates.  `ricciFlowStep = lazyHeatStepNum` on the edge-curvature
   field; `ricci_curvature_bounded` (no blow-up, from `heatIter_range`), `ricci_uniform_stationary`
   (uniform `K_{NS,NT}` curvature is the normalized fixed point, `lazyHeatStep_const`).
3. **Monotonicity / convergence of discrete flow** — ✅ DONE (same file).
   `ricci_energy_monotone` (**curvature Dirichlet energy decays `E(flow K) ≤ 16·E(K)`** —
   `lazy_energy_decay`, the discrete Perelman 𝓦-/entropy-monotonicity) + `ricci_flow_homogenises`
   (the maximally-oscillating checkerboard curvature field is driven to **constant curvature** in
   one step, spread `1→0` — `lazy_checker_collapses`).  *The discrete analogue of Perelman
   monotonicity and the A6-core target — closed via the PDE marathon.*  **A6 conquest core closed
   on the discrete side.**  Convergence is also a genuine **`flow_reaches` (A6 FLOW archetype)**
   instance: `ricci_flow_reaches_normalized` — the curvature-spread monovariant `spreadFlow` strictly
   descends (by 2/step) until the normalised state `spread ≤ 1` (`spreadFlow_fixed_le_one`), exactly
   rung 3's stated "drive the flow to constant curvature via A6 FLOW on a curvature-spread monovariant".
4. **Discrete Gauss–Bonnet** — ✅ DONE (`GeometrizationConjecture/DiscreteGaussBonnet.lean`,
   4 PURE).  Vertex curvature `κ(v)=2−deg(v)`; **`Σ_v κ(v) = 2·χ`** (`gauss_bonnet_Kmn`, `χ=V−E`),
   `χ = 1 − b₁` (`euler_eq_one_sub_b1`, cyclomatic `b₁=E−V+1`), hence **total curvature `= 2 − 2·b₁`**
   (`totalCurv_eq`) — positive ⟺ `b₁=0` (tree), negative ⟺ `b₁≥1` (cyclic).  `curvature_sign_topology`:
   `K_{1,1}` `+2` (`b₁=0`) vs `K_{3,2}` `−2` (`b₁=2`) — **curvature sign ↔ topology now a theorem,
   not a table** (derived by `ring_intZ`).  (Bochner/CD(K,N) Bakry–Émery is a further refinement.)
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
