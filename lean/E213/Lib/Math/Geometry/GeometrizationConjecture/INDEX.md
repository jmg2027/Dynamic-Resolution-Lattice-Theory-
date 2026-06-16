# GeometrizationConjecture — sub-tree INDEX

213-Lens reading of the Thurston/Perelman Geometrization conjecture
and the dimension-4 exotic-smoothness anomaly.

**Status**:
  · **G121 R1 CLOSED** at ~149 PURE / 0 DIRTY across 25 steps (2026-05-22)
  · **G121 R1+ PARTIAL** for G123/G124/G125 (2026-05-22 extension)


## File map

### Core (G121 R1, CLOSED)

| File | Steps | PURE | Content |
|---|---|---|---|
| `Ansatz.lean` | 1-3 | ~23 | Core defs (`chartBase`, `selfPointingAxes`, `chartVisibleAxes`) + axiom-level shadow + parametric δ⁰-kernel deployment |
| `M1Routes.lean` | 4, 5, 8 | ~7 | M1 atomicity + cohomology route + c=2 Möbius forcing |
| `ScopeAndDepth.lean` | 7, 9, 10 | ~28 | Cohomology-route scope correction + depth filter (Sym(3) + c=2 binary cover) |
| `DimSpectrum.lean` | 6, 14 | ~14 | Geometrization dim spectrum d_M ∈ {3..6} + Sym(3)-capable enumeration |
| `Poincare.lean` | 12, 13, 15 | ~31 | Poincaré pillar (tree + corrected Euler + Generalized + Filled) |
| `Ricci.lean` | 16, 17 + I-3 | ~21 | Ricci modulus (BracketCauchy parallel) + fixed-point characterisation + saturation cap + bijection on reachable range + composition semantics + ★★★★★★★ `I3_ricci_eps_lens_deepening_close` |
| `EightGeometries.lean` | 11, 18-22 | ~30 | 8 model geometries via single Möbius P + 3 Lenses (ℝ/ℤ/F_5) |
| `StructuralMapping.lean` | 21, 23, 24 | ~14 | octet-8 + universal-8 + ★★★★★★★★★★ ultimate structural mapping |
| `Capstone.lean` | 25 | ~5 | d=4 info richness + ★★★★★★★★★★★ `R1_close_certificate` |

### R1+ Extensions (G123/G124/G125 partials)

| File | Target | PURE | Content |
|---|---|---|---|
| `Generalization.lean` | G124 (G123 FW-3) | ~14 | K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended + ★★★★★ universal Prop-level closure (`sym3_c2_force_K32`, `sym3_c2_iff_K32_or_K23`, `filter_passes_only_chartBase_5`) — supersedes per-chartBase enumeration |
| `JsjDeep.lean` | FW-2 | ~205 | JSJ 3-cell complex Euler-target scaffold + cycle inventory (9 atomic, rank 8) + concrete (k, j) attaching + bipartite S/T → JSJ torus + FW-2 unbounded + concrete 3-mfd target attaching maps + L(p, q) parameter family + L(p, q) classification refinement + connected sum + PURE universal k − j = 7 preservation + multi-fold connected sums + Heegaard splitting genus + **Heegaard additivity** (`targetListGenus` summing `heegaardGenus` over target list; bridge to `multiHeegaardGenus`) + **lens space linking number** (`lensLinkingNumber p q = q`; lensHomotopyEquiv via QR mod p; L(7,1) ≃ L(7,2) homotopy yes / homeo no) + ★★★★★★★★ multiple capstones (FW2_concrete, Lpq_parameter_family, connectedSum_and_Lpq_refinement, connectedSum_universal, multi_fold_connected_sum, heegaard_genus, heegaard_additivity, lens_space_invariants) |
| `MetricGeometries.lean` | FW-4 + 8-geo Lie + cross-frame | ~58 | mod-k Möbius P Lens family + F_5 Nil uniqueness + curvature sign / isometry-group dim / Lie group dim per geometry + 6-class Lie partition + center-dim totals + **geometric structure ↔ Lie group consolidation** (`isLieGroupGeometry`, 6 Lie + 2 product = 8 partition, joint isotropic/anisotropic cross-frame) + ★★★★★★★ `FW4_direct_realization_close` + `eight_geo_lie_group_infra_close` + `geometric_structure_lie_group_consolidation` |
| `CrossFrame.lean` | G123 X-1 + I-1 | ~5 | ★★★★★★ `X1_sym3_cross_frame_capstone` (4-way Sym(3) convergence) + ★★★★★ `sym3_basis_thurston_mapping` (explicit basis ↔ Thurston geometry mapping with +1/-1 reshape arithmetic) |
| `Exotic4Mfd.lean` | G123 FW-1 substantive + sub-orbit | ~33 | `sym3GaugeInvariant` + ★★★★★★ `exotic_4mfd_scaffold` + per-element fix counts (`fixedSizeS01/S12/S02/Rho = 32, 32, 32, 4`) + Burnside `sym3OrbitCount = 60` + ★★★★★★ `fw1_suborbit_decomposition` `(4, 0, 28, 28)` |
| `KChartLensAbstract.lean` | M2 abstract + universal close + d_M=4 synthesis | ~20 | `KChartLens NS NT c` structure + canonical instances (`K32_chart_lens`, `K31_chart_lens`, `K14_chart_lens`) + ★★★★★ `m2_abstract_close` + **universal M2**: `forcedKChartLens` (connectedness forces `selfPointingAxes = 1`, `chartVisibleAxes = chartBase − 1` for arbitrary connected K via `Parametric.Betti.KernelConstancyUniversal`) + ★★★★★★ `m2_universal_forced_partition` + ★★★★★★★ `dM_four_via_M1_forced_and_M2_universal_kernel` (M1 forced chartBase 5 ∘ M2 derived 1-dim kernel → d_M = 4) + `every_dimension_realized` + ★★★★★★★ `criticality_is_forcing_not_kernel` (d_M=4 criticality = M1 forcing, M2 kernel is dimension-uniform) + ★★★★★★★★★★★ `geometrization_followup_close_certificate` |
| `Poincare.lean` (+ I-4) | G123 I-4 | +1 | ★★★★ `poincare_two_layer_trivial_loop` — two-layer reading (b₀ + b₁) via `Delta0AndConnectedness.b0_K32_c2` |

### A6 discrete Ricci core (discrete Forman/Ollivier + smooth 2D-conformal route)

The 213-native A6 Ricci-flow core: combinatorial curvature needing no smooth
manifold (Forman / Ollivier) plus the smooth 2D-conformal sidestep.  Narrative:
`theory/essays/synthesis/curvature_as_lens_readout.md`.

| File | Rung | PURE | Content |
|---|---|---|---|
| `DiscreteRicci.lean` | 1 | 5 | Forman edge curvature `4 − du − dv`; `K_{NS,NT}` uniform value; sign ↔ `b₁` (`forman_K11/K13/K32`, `discrete_curvature_topology`) |
| `RicciFlowDiscrete.lean` | 2-3, 7, 12 | 17 | `ricciFlowStep = lazyHeatStepNum`; a-priori bundle (bounded, total-curvature-conserved, energy-monotone = Perelman 𝓦); `ricci_flow_reaches_normalized` (flow_reaches → constant curvature); §6 `ricci_flow_fixed_point_stable`; §7 `ricci_chi_entropy_monotone` (χ²-divergence from the round state non-increasing) |
| `DiscreteGaussBonnet.lean` | 4 | 4 | Vertex curvature `2 − deg`; `Σκ = 2χ` (`gauss_bonnet_Kmn`); total `= 2 − 2b₁`; `curvature_sign_topology` |
| `OllivierRicci.lean` | 5 | 29 | Optimal-transport engine (`kantorovich_weak_duality` + `ollivier_plan_optimal`, on the `gridSumZ` toolkit from `Combinatorics/IntGridSum`); full sign trichotomy: triangle `κ=½` / square `κ=0` / double-star `κ=−2/3` |
| `BakryEmery.lean` | 6 | 6 | Fourth curvature frame: carré-du-champ `Γ`/`Γ₂`; discrete **Bochner identity** (`bochner_line`/`bochner_triangle`); `CD(0,2)` (line) + `CD(5/2,∞)` (triangle `K₃`) — synthetic `Ric ≥ K, dim ≤ N` |
| `BakryEmeryBipartite.lean` | 6 (K_{a,b}) | 9 | General bipartite `K_{a,b}` Bakry–Émery: two-shell Bochner + shell-SOS; wide (`b ≥ 2a−2`) / narrow (Cauchy–Schwarz) regimes; `K_{3,2} = CD(3/2,∞)` |
| `DiscreteLichnerowicz.lean` | spectral + §4 | 18 | Curvature → spectrum: `km_rayleigh` (`Σ(Lf)² = m·E`), `K_m` spectrum `{0, m}` + eigenspaces, `lichnerowicz_abstract` (`K ≤ λ`); §4 **gradient-semigroup commutation** `Γ(P_c u) = (c−m)²·Γ(u)` (exact) + `km_be_gradient_estimate` (the `CD((m+2)/2)`-rate Bochner-with-Ricci estimate) |
| `ConformalCurvature.lean` | S3-S5 | 6 | Smooth 2D-conformal Liouville `K=(\|∇λ\|²−λΔλ)/(2λ³)` for polynomial `λ`; `conformal_curvature_trichotomy`; flow fixed point ⟺ flat |
| `WeightedGreen.lean` | wall (i) | 11 | **Weighted IBP**: `weighted_green` (`⟨f,g⟩_w = −2Σg·L_w f`, weight = Perelman `e^{−f}` measure); `dirichlet_gradient_identity` (the flow IS the gradient flow of `𝓕_w`); SOS descent rate; mass conservation |
| `DiscreteGaussian.lean` | wall (ii)+(iii)+NLC | 11 | Binomial heat kernel: `gaussian_normalization` (`Σu(t,·) = 2^t` ∀t, the `(4πτ)^{−n/2}` content); `gaussian_mean`; `gaussian_li_yau` (log-concavity = Li–Yau gradient estimate, division-free); `harnack_forward`; §4 **no-local-collapsing** `2^{2n} ≤ (2n+1)·u(2n,n)` + `kernel_density_pinch` |
| `DiscreteSurgery.lean` | wall (iv) | 15 | Surgery ledger: `gauss_bonnet_general` (any graph, handshake ⟹ `Σκ=2χ`); cut-a-neck `χ+1`/curvature `+2`; `surgery_dichotomy` (round XOR neck-bearing); A6 termination + **exact count** `= b₁`; `k32_surgery` (`−2→0→+2`) |

## Supporting infrastructure (outside sub-tree, referenced from above)

| File | Purpose | PURE |
|---|---|---|
| `Cohomology/Bipartite/Filled3Cell.lean` | `Cell3ComplexK32` parametric 3-cell extension structure (k 2-cells + j 3-cells, χ computation, closed 3-mfd realization predicate) | 21 |
| `Geometry/MetricTypes.lean` | 213-native `MetricSignature` + `LensChoice` + `classify` for 8 Thurston geometries; F_5 → Nil uniqueness at signature level | 16 |

## Pillar status (5-pillar Geometrization)

| Pillar | 213-Lens form | Status |
|---|---|---|
| 8 geometries | Möbius P + 3 Lenses (ℝ/ℤ/F_5) ↔ Sym(3) decomp (2·trivial + 3·standard) | ★★★★★★ COMPLETE ✅ |
| JSJ | bipartite S/T + Filled cells (+JsjDeep χ-targets) | PARTIAL ✓ (G123 partial) |
| Poincaré | K_{3,1}^{(c=1)} unique tree + S³ = ∂Δ⁴ | DOUBLY REALIZED ✅ |
| Generalized Poincaré | K_{1,k}^{(c=1)} all chartBase | GENERALIZED ✅ |
| Ricci flow | `K32_ricci_modulus` averaging | PARTIAL CLOSE ✅ |

## Marathon-candidate status

| ID | Topic | Initial | R1+ |
|---|---|---|---|
| G122 | 4-mfd exotic enumeration via Sym(3) gauge | OPEN | OPEN (new marathon) |
| G123 | JSJ 3-cell complex extension | OPEN | **PARTIAL** (`JsjDeep.lean`) |
| G124 | K_{NS,NT}^{(c)} generalization | OPEN | **PARTIAL** (`Generalization.lean`) |
| G125 | E³/H³/H²×ℝ direct realization | OPEN | **PARTIAL** (`MetricGeometries.lean`) |

## Möbius P Lens family (R1+ extension)

Step 22's F_5 Nil insight extended to 5 mod-k Lens readings:

| Modulus | Polynomial mod p | Geometric narrative |
|---|---|---|
| ℝ | distinct irrational roots | H², H³, Sol |
| ℤ | det = 1 (SL(2,ℤ)) | ~SL₂(ℝ) |
| F_2 | irreducible (x² + x + 1) | E³ candidate (flat) |
| F_3 | irreducible (x² + 1) | H²×ℝ candidate |
| F_5 | (λ+1)² double root | Nil ✅ (user-derived) |
| F_7 | irreducible (5 not square) | H³ candidate |
| F_11 | reducible (4² = 5 mod 11) | split-geometry candidate |

**One algebraic source (Möbius P), seven Lens readings, eight
geometric narratives**.

## Dependency chain

```
Ansatz
   └── M1Routes
         └── ScopeAndDepth
                └── DimSpectrum
                       └── Poincare
                              └── Ricci
                                    └── EightGeometries
                                          └── StructuralMapping
                                                └── Capstone
                                                      └── Generalization
                                                            └── JsjDeep
                                                                  └── MetricGeometries
                                                                        └── CrossFrame
                                                                              └── Exotic4Mfd
                                                                                    └── KChartLensAbstract
```

Linear chain (each file imports previous one).
All under namespace `E213.Lib.Math.Geometry.GeometrizationConjecture.ChartAxisAnsatz`.

## Open knots (G121 §6)

| Knot | Status |
|---|---|
| M1 (why $d_{213}=5$) | TWO-ROUTE CLOSE (atomicity + Möbius); universal closure via `sym3_c2_force_K32` (chartBase-free) |
| M2 (chart count = $d-1$) | UNIVERSAL CLOSE (structural): `Parametric.Betti.KernelConstancyUniversal` proves δ⁰-kernel = constant cochains (dim 1) for every connected K (NS≥1, NT≥1, c≥1), ∅-axiom; `forcedKChartLens` / `m2_universal_forced_partition` force `selfPointingAxes = 1`, `chartVisibleAxes = chartBase − 1` |
| M3 (NT axis split) | downstream (physics interpretation) |
| M4 (KK firewall) | doc-level stereotype warnings |
