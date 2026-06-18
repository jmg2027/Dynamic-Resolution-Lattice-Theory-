# DiscreteCurvature — sub-tree INDEX

A discrete (and 2D-conformal smooth) differential-geometry library, all
`∅`-axiom over `ℤ`/`ℕ`: combinatorial curvature, the discrete Bochner
identity, optimal-transport curvature, the spectral bridge, the binomial
heat kernel, graph surgery, and homogeneous Ricci flow.

Narrative: `theory/math/geometry/discrete_curvature.md`.

## Combinatorial curvature

| File | Content |
|---|---|
| `DiscreteRicci.lean` | Forman edge curvature `4 − du − dv`; uniform value on `K_{m,n}`; sign ↔ cyclomatic `b₁` (`forman_K11/K13/K32`, `discrete_curvature_topology`) |
| `DiscreteGaussBonnet.lean` | Vertex curvature `2 − deg`; `Σκ = 2χ` (`gauss_bonnet_Kmn`); total `= 2 − 2b₁`; `curvature_sign_topology` |
| `OllivierRicci.lean` | Optimal-transport engine (`kantorovich_weak_duality` + `ollivier_plan_optimal`, on the `gridSumZ` toolkit); sign trichotomy: triangle `κ=½` / square `κ=0` / double-star `κ=−2/3` |
| `BakryEmery.lean` | Carré-du-champ `Γ`/`Γ₂`; discrete **Bochner identity** (`bochner_line`/`bochner_triangle`); `CD(0,2)` (line) + `CD(5/2,∞)` (triangle `K₃`) |
| `BakryEmeryBipartite.lean` | General bipartite `K_{a,b}` Bakry–Émery: two-shell Bochner + shell-SOS; wide / narrow regimes; `K_{3,2} = CD(3/2,∞)` |
| `DiscreteLichnerowicz.lean` | Curvature → spectrum: `km_rayleigh` (`Σ(Lf)² = m·E`), `K_m` spectrum `{0,m}` + eigenspaces, `lichnerowicz_abstract` (`K ≤ λ`); §4 gradient-semigroup commutation + `km_be_gradient_estimate` |

## Flows, heat kernel, surgery

| File | Content |
|---|---|
| `RicciFlowDiscrete.lean` | `ricciFlowStep = lazyHeatStepNum`; a-priori bundle (bounded, total-curvature-conserved, energy-monotone); `ricci_flow_reaches_normalized`; fixed-point stability; χ²-divergence monotone |
| `DiscreteGaussian.lean` | Binomial heat kernel: `gaussian_normalization` (`Σu(t,·)=2^t` ∀t), `gaussian_mean`, `gaussian_li_yau` (log-concave Li–Yau), `harnack_forward`; §4 no-local-collapsing density pinch |
| `WeightedGreen.lean` | Weighted IBP: `weighted_green` (`⟨f,g⟩_w = −2Σg·L_w f`); `dirichlet_gradient_identity` (the flow is the gradient flow of the weighted Dirichlet energy); SOS descent; mass conservation |
| `DiscreteSurgery.lean` | Surgery ledger: `gauss_bonnet_general` (any graph, handshake ⟹ `Σκ=2χ`); cut-a-neck `χ+1`/curvature `+2`; `surgery_dichotomy` (round XOR neck); termination + exact count `= b₁`; `k32_surgery` |

## Smooth route

| File | Content |
|---|---|
| `ConformalCurvature.lean` | Smooth 2D-conformal Liouville `K=(\|∇λ\|²−λΔλ)/(2λ³)` for polynomial `λ`; `conformal_curvature_trichotomy`; flow fixed point ⟺ flat |
| `RicciFlow.lean` | Monovariant cell-filling flow on `K_{3,2}` (b₁: 8→5) converging to a maximally-filled normal form via the FLOW archetype (`MonovariantFlow.flow_reaches`) |
| `RicciSphereFlow.lean` | Round `Sⁿ` smooth-metric Ricci flow → finite extinction (homogeneous/ODE case; rate = `Ric=(n−1)g`) |
| `RicciHomogeneous.lean` | Homogeneous Ricci flow Einstein trichotomy: `λ>0` finite extinction / `λ=0` stationary / `λ<0` divergence |

## Supporting infrastructure (outside sub-tree)

  · `Lib/Math/Combinatorics/IntGridSum` — `gridSumZ` + Fubini, the integer-grid sum toolkit.
  · `Lib/Math/Combinatorics/Binomial` — Pascal recursion for the heat kernel.
  · `Lib/Math/Analysis/ODE/HeatEq/*` — discrete heat-equation a-priori estimates.
  · `Lib/Math/Foundations/MonovariantFlow` — the well-founded-descent FLOW lift.
