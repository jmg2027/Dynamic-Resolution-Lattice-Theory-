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
5. **Ollivier–Ricci** — ✅ **DONE** (`GeometrizationConjecture/OllivierRicci.lean`, ∅-axiom):
   the optimal-transport engine.  `gridSumZ` (Int grid sum) + `gridSumZ_fubini` (sum-swap) →
   **`kantorovich_weak_duality`** (`Σ f·μ − Σ f·ν ≤ Σ Σ d·π` for any coupling `π≥0` and `1`-Lipschitz
   `f` — the `W₁`-dual ≤ `W₁`-primal direction), and `ollivier_bracket` (`1−transportCost ≤ 1−dualValue`,
   the curvature lower/upper bracket that pins `κ` when a plan and a potential meet).  **Concrete `κ`
   now exhibited**: the triangle `C₃` worked example — `triangle_coupling` (the `triPi` plan's marginals
   are `triMu0`/`triMu1`), `triF_lipschitz` (the `triF` potential is `1`-Lipschitz), and
   `triangle_ollivier_optimal` (`dualValue = transportCost = 1`, plan meets potential) — pins the scaled
   `W₁ = 1`, hence Ollivier `κ = 1 − ½ = ½ > 0`: **the triangle is positively curved**, a concrete
   value, not just the bracket.  Upgraded to a **genuine optimum**: `ollivier_plan_optimal` (general —
   `dualValue` depends only on marginals, so a plan meeting any `1`-Lipschitz dual is cost-optimal among
   all plans with its marginals) + `triangle_plan_optimal` (`triPi`'s cost `1 ≤` cost of *every* valid
   coupling of `m₀,m₁`).  **Sign contrast now a theorem pair**: the square `C₄` worked example
   (`c4D`/`c4Pi`/`c4F` + `c4_coupling`/`c4_ollivier_flat`/`c4_plan_optimal`) gives Ollivier `κ = 0`
   (flat, no triangles), against the triangle's `κ = ½ > 0` (clustered) — Ollivier curvature tracks local
   clustering, the optimal-transport analogue of the Forman / Gauss–Bonnet sign↔topology results.  **Full
   sign trichotomy now closed**: the double-star (`dsD`/`dsPi`/`dsF` + `ds_coupling`/`ds_ollivier_negative`/
   `ds_plan_optimal`, helper `sub_le_sub_bounds`) gives Ollivier `κ = 1 − 5/3 = −2/3 < 0` (a tree, like
   hyperbolic space) — so `+` (triangle, clustered) / `0` (square, flat) / `−` (double-star, tree) are all
   ∅-axiom theorems, the complete Ollivier mirror of the Forman / Gauss–Bonnet sign↔topology trichotomy.
6. **Bakry–Émery curvature-dimension `CD(K,N)`** — ✅ **DONE** (`GeometrizationConjecture/BakryEmery.lean`,
   6 PURE): the **fourth** curvature frame, via the discrete Bochner formula.  Carré du champ `Γ` + its
   iterate `Γ₂` of the graph Laplacian, scaled to `ℤ` (`gammaL`/`gamma2L`, `gammaTri`/`gamma2Tri`).
   **Discrete Bochner identity** `bochner_line` (`4Γ₂ = (Lf(x−1))² + 2(Lf(x))² + (Lf(x+1))²` — the flat
   `Ric = 0` Bochner, `½Δ|∇f|² = |Hess f|² + Ric(∇f,∇f)` with only squares) ⟹ `cd_0_2_line` (the
   line/large cycle is `CD(0,2)`, curvature `0`) + `gamma2_line_nonneg`.  `bochner_triangle`
   (`4Γ₂ = 5·(2Γ) + 2(f₁−f₂)²`, i.e. `Γ₂ = (5/2)Γ + ½(f₁−f₂)²`) ⟹ `cd_triangle` (the triangle `C₃ = K₃` is
   `CD(5/2,∞)`, the complete-graph value `(n+2)/2`).  This is the *dimension-independent* curvature frame
   (`CD(K,N)` = synthetic `Ric ≥ K, dim ≤ N`, Lott–Sturm–Villani), so it is the 213-native handle for the
   general-`n` Ricci **lower bound** even while the smooth `n`-tensor flow stays walled
   (`ricci_flow_smooth_core.md`).  Sign agreement: flat line `K=0` / triangle `K=5/2>0` — same pattern as
   Forman, Gauss–Bonnet, Ollivier.
7. **Time-evolution: all-time fixed-point stability** — ✅ **DONE** (`RicciFlowDiscrete.lean` §6):
   `lazyRicciFlow` (the smoothing step iterated) + `ricci_flow_fixed_point_stable`
   (`lazyRicciFlow n t (constInit c) x = 4ᵗ·c` for *every* `t` — constant curvature is a genuine all-time
   fixed point, the discrete "round/Einstein metric stays round under Ricci flow for all time", complementing
   rung 3's `flow_reaches` *to* the fixed point).

## Honest boundary

This closes A6's core **in the discrete (Forman/Ollivier) theory** — a genuine
parallel mathematics, not smooth Perelman.  The smooth core stays walled
(`ricci_flow_smooth_core.md`).  The claim to make: "A6 FLOW drives discrete
Ricci flow to its normalized fixed point" — not "A6 solves Poincaré."

## Next action

**Rungs 1–7 all ✅ DONE** (Forman flow + a-priori package + Gauss–Bonnet + Ollivier transport core with
full `+/0/−` trichotomy + Bakry–Émery `CD(K,N)` Bochner identity + all-time fixed-point stability).  The
discrete A6 core is closed across **four** curvature frames (Forman, Gauss–Bonnet, Ollivier, Bakry–Émery),
all sign-agreeing.

**Rung 6 refinement — the complete graph `K_m` for general `m`** — ✅ **DONE**
(`BakryEmery.lean` §3, 14 PURE: 6 defs + 8 theorems).  The triangle `bochner_triangle` was the `m = 3`
case; §3 discharges the whole family parametric in the vertex count.  `K_m` is modelled as a **centre vertex** (value `c`) joined
to `k = m−1` **neighbours** (`b : Nat → Int`), every pair also adjacent — a presentation that makes the
positive-curvature term a **full double `gridSumZ` of squared differences** `sosGap = Σ_jΣ_{j'}(b j'−b j)²`
whose diagonal `(b j − b j)² = 0` vanishes on its own, so **no index has to be excluded** (the bookkeeping
wall the `m = 3` hand computation only sidestepped concretely, and a Cauchy–Schwarz route would have hit).
`bochner_complete` (`gamma2C = (k+3)·gammaC + sosGap`, pure `gridSumZ` linearity + `ring_intZ`) ⟹
`cd_complete_graph` (`gamma2C ≥ (k+3)·gammaC`, from `sosGap_nonneg`): **`K_m` is `CD((m+2)/2, ∞)`** since
`k+3 = m+2`, the textbook Bakry–Émery curvature of the complete graph, generalizing `cd_triangle`
(`k = 2`: `k+3 = 5`, `sosGap = 2(b₀−b₁)²`).  The bound is **sharp** (`cd_complete_graph_sharp`): on any
constant-neighbour configuration `sosGap = 0`, so `gamma2C = (k+3)·gammaC` *exactly* — `(m+2)/2` is the
*actual* curvature of `K_m`, not just a lower bound, hence cannot be improved.  New generic infra:
`gridSumZ_const`, `gridSumZ_nonneg` (`OllivierRicci.lean` §1).

**Rung 5 refinement — Ollivier `κ` for the complete graph `K_m`, general `m`** — ✅ **DONE**
(`OllivierRicci.lean` §7, parametric, PURE).  The optimal-transport companion of the Bakry–Émery `K_m`
above: the edge `(0,1)` of `K_m`, walk measures `m₀,m₁` differing only at `0,1` (they share the `m−2`
neighbours `{2,…,m−1}`).  The plan `kmPi` keeps the shared units on the diagonal and moves the single unit
`1 ↦ 0` (cost `1`); the `δ₁` potential `kmF` reaches dual value `1`.  `km_cost`/`km_dual` (each a
`gridSumZ`-`δ` computation parametric in `m`, **not** `decide` on a fixed graph) ⟹ `km_ollivier_optimal`
(meet: `dualValue = transportCost = 1`) + `km_plan_optimal` (cost `≤` every coupling, via `km_coupling` +
`kmF_lipschitz`): scaled `W₁ = 1`, so **Ollivier `κ = 1 − 1/(m−1) = (m−2)/(m−1) > 0`** for `K_m` (`m ≥ 3`),
generalizing the §4 triangle (`m = 3`, `κ = ½`) and `→ 1` as `m → ∞`.  New generic infra: the Kronecker-`δ`
grid sums `gridSumZ_delta`, `gridSumZ_delta_zero`, `gridSumZ_delta_weight` (`OllivierRicci.lean` §1).  Both
general-`m` complete-graph curvatures (Bakry–Émery `CD((m+2)/2,∞)` + Ollivier `(m−2)/(m−1)`) now stand.

**Lin–Yau optimal `K` for `K_m`** — ✅ **DONE** (`BakryEmery.lean` §3, `lin_yau_curvature_complete`).
The lower bound `cd_complete_graph` is *attained with equality* on the constant-`0` neighbour
configuration (`cd_complete_graph_sharp`), which is **non-vacuous** — `complete_graph_gammaC_witness`
gives `gammaC = k > 0` for `k = m−1 ≥ 1`.  Lower bound + tight witness ⟹ `(m+2)/2` is the *optimal*
(Lin–Yau) Bakry–Émery curvature of `K_m`, not merely a bound.

**Bipartite star `K_{1,b}` Bakry–Émery** — ✅ **DONE** (`BakryEmery.lean` §4, PURE).  The first bipartite
case `K_{a,b}` with `a = 1`: a centre joined to `b = k` leaves, **no leaf–leaf edges** (triangle-free).
Reuses the centre operators `lapC`, `gammaC`; only the *leaf* operators change (a leaf's sole neighbour is
the centre, so `lapLeaf = c − b j`, `gammaLeaf = (c − b j)²` — **no** other-neighbour sum, unlike `K_m`'s
mutually-adjacent neighbours).  `bochner_star` (`gamma2Star = (3 − b)·gammaC + 2·lapC²`, `2·lapC² ≥ 0` SOS)
⟹ `cd_star` (`CD((3−b)/2, ∞)`).  **Sign trichotomy in the leaf count `b`**: `b ≤ 2` positive, `b = 3`
flat, `b ≥ 4` **negative** (`star_negatively_curved`: `3 − b < 0`) — a hub/tree is negatively curved,
matching the double-star Ollivier `κ = −2/3 < 0` (`OllivierRicci` §6) and *opposite* the clique `K_m`
(`CD((m+2)/2,∞) > 0`): adding leaf–leaf edges (star → clique) flips curvature sign, the clustering `Γ₂`
measures.  **Still open**: general `K_{a,b}` (`a ≥ 2`) needs a **second-shell** (`a−1` other `A`-vertices)
optimization (`Lf(w) − Lf(v)` is not proportional to `(w − v)`), heavier than the star.

Remaining refinements: general bipartite `K_{a,b}` (`a ≥ 2`, the DRLT `K_{3,2}` core, two-shell); the
discrete Lin–Yau optimal `K` for the cycle; more concrete Ollivier `κ` on further graphs.  Still walled: the smooth general-`n` *tensor
flow* and the transcendental Perelman `𝓦`-entropy (`ricci_flow_smooth_core.md`) — but the general-`n` Ricci
**lower bound** is now reachable synthetically via `CD(K,N)` (rung 6, now for *every* `K_m`).  The smooth
2D-conformal route (S3–S5) is separately closed (`ConformalCurvature.lean`).
