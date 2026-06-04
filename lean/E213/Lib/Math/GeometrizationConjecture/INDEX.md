# GeometrizationConjecture — sub-tree INDEX

213-Lens reading of the Thurston/Perelman Geometrization conjecture
and the dimension-4 exotic-smoothness anomaly.

**Status**:
  · **G121 R1 CLOSED** at ~149 PURE / 0 DIRTY across 25 steps (2026-05-22)
  · **G121 R1+ PARTIAL** for G123/G124/G125 (2026-05-22 extension)

Cross-reference: `research-notes/frontiers/G121_dim4_self_pointing_axis.md`.

## File map

### Core (G121 R1, CLOSED)

| File | Steps | PURE | Content |
|---|---|---|---|
| `Ansatz.lean` | 1-3 | ~23 | Core defs (`chartBase`, `selfPointingAxes`, `chartVisibleAxes`) + axiom-level shadow + V32Betti deployment |
| `M1Routes.lean` | 4, 5, 8 | ~7 | M1 atomicity + cohomology route + c=2 Möbius forcing |
| `ScopeAndDepth.lean` | 7, 9, 10 | ~28 | Cohomology-route scope correction + depth filter (Sym(3) + c=2 binary cover) |
| `DimSpectrum.lean` | 6, 14 | ~14 | Geometrization dim spectrum d_M ∈ {3..6} + Sym(3)-capable enumeration |
| `Poincare.lean` | 12, 13, 15 | ~31 | Poincaré pillar (tree + corrected Euler + Generalized + Filled) |
| `Ricci.lean` | 16, 17 + I-3 | ~21 | Ricci modulus (BracketCauchy parallel) + fixed-point characterisation + saturation cap + bijection on reachable range + composition semantics + ★★★★★★★ `I3_ricci_eps_lens_deepening_close` |
| `EightGeometries.lean` | 11, 18-22 | ~30 | 8 model geometries via single Möbius P + 3 Lenses (ℝ/ℤ/F_5) |
| `StructuralMapping.lean` | 21, 23, 24 | ~14 | HC_K32 + universal-8 + ★★★★★★★★★★ ultimate structural mapping |
| `Capstone.lean` | 25 | ~5 | d=4 info richness + ★★★★★★★★★★★ `R1_close_certificate` |

### R1+ Extensions (G123/G124/G125 partials)

| File | Target | PURE | Content |
|---|---|---|---|
| `Generalization.lean` | G124 (G123 FW-3) | ~14 | K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended + ★★★★★ universal Prop-level closure (`sym3_c2_force_K32`, `sym3_c2_iff_K32_or_K23`, `filter_passes_only_chartBase_5`) — supersedes per-chartBase enumeration |
| `JsjDeep.lean` | FW-2 | ~205 | JSJ 3-cell complex Euler-target scaffold + cycle inventory (9 atomic, rank 8) + concrete (k, j) attaching + bipartite S/T → JSJ torus + FW-2 unbounded + concrete 3-mfd target attaching maps + L(p, q) parameter family + L(p, q) classification refinement + connected sum + PURE universal k − j = 7 preservation + multi-fold connected sums + Heegaard splitting genus + **Heegaard additivity** (`targetListGenus` summing `heegaardGenus` over target list; bridge to `multiHeegaardGenus`) + **lens space linking number** (`lensLinkingNumber p q = q`; lensHomotopyEquiv via QR mod p; L(7,1) ≃ L(7,2) homotopy yes / homeo no) + ★★★★★★★★ multiple capstones (FW2_concrete, Lpq_parameter_family, connectedSum_and_Lpq_refinement, connectedSum_universal, multi_fold_connected_sum, heegaard_genus, heegaard_additivity, lens_space_invariants) |
| `MetricGeometries.lean` | FW-4 + 8-geo Lie + cross-frame | ~58 | mod-k Möbius P Lens family + F_5 Nil uniqueness + curvature sign / isometry-group dim / Lie group dim per geometry + 6-class Lie partition + center-dim totals + **geometric structure ↔ Lie group consolidation** (`isLieGroupGeometry`, 6 Lie + 2 product = 8 partition, joint isotropic/anisotropic cross-frame) + ★★★★★★★ `FW4_direct_realization_close` + `eight_geo_lie_group_infra_close` + `geometric_structure_lie_group_consolidation` |
| `CrossFrame.lean` | G123 X-1 + I-1 | ~5 | ★★★★★★ `X1_sym3_cross_frame_capstone` (4-way Sym(3) convergence) + ★★★★★ `sym3_basis_thurston_mapping` (explicit basis ↔ Thurston geometry mapping with +1/-1 reshape arithmetic) |
| `Exotic4Mfd.lean` | G123 FW-1 substantive + sub-orbit | ~33 | `sym3GaugeInvariant` + ★★★★★★ `exotic_4mfd_scaffold` + per-element fix counts (`fixedSizeS01/S12/S02/Rho = 32, 32, 32, 4`) + Burnside `sym3OrbitCount = 60` + ★★★★★★ `fw1_suborbit_decomposition` `(4, 0, 28, 28)` |
| `KChartLensAbstract.lean` | G123 M2 abstract + close certificate | ~11 | `KChartLens NS NT c` structure + canonical instances (`K32_chart_lens`, `K31_chart_lens`, `K14_chart_lens`) + ★★★★★ `m2_abstract_close` + ★★★★★★★★★★★ `geometrization_followup_close_certificate` (33-conjunct mega-capstone bundling all 10 follow-up items) |
| `Poincare.lean` (+ I-4) | G123 I-4 | +1 | ★★★★ `poincare_two_layer_trivial_loop` — two-layer reading (b₀ + b₁) via `V32Betti.b0_eq_1` |

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
All under namespace `E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz`.

## Open knots (G121 §6)

| Knot | Status |
|---|---|
| M1 (why $d_{213}=5$) | TWO-ROUTE CLOSE (atomicity + Möbius); universal closure via `sym3_c2_force_K32` (chartBase-free) |
| M2 (chart count = $d-1$) | ABSTRACT CLOSE via `KChartLens NS NT c` + V32Betti compatibility for K_{3,2}^{(c=2)} |
| M3 (NT axis split) | downstream (physics interpretation) |
| M4 (KK firewall) | doc-level stereotype warnings |
