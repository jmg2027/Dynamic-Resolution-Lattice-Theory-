# GeometrizationConjecture — sub-tree INDEX

213-Lens reading of the Thurston/Perelman Geometrization conjecture
and the dimension-4 exotic-smoothness anomaly.

**Status**: G121 R1 CLOSED at ~149 PURE / 0 DIRTY across 25
development steps (2026-05-22).

Cross-reference: `research-notes/G121_dim4_self_pointing_axis.md`.

## File map

| File | Steps | PURE | Content |
|---|---|---|---|
| `Ansatz.lean` | 1-3 | ~23 | Core defs (`chartBase`, `selfPointingAxes`, `chartVisibleAxes`) + axiom-level shadow via `Meta.LensInternality` + deployment-level M2 via `V32Betti.kerSizeDelta0_eq_2` |
| `M1Routes.lean` | 4, 5, 8 | ~7 | M1 atomicity (`TriangleIteration`) + M1 cohomology route (`TopologyCompare`) + c=2 Möbius forcing (`C2DoublingDerivation`) |
| `ScopeAndDepth.lean` | 7, 9, 10 | ~28 | Cohomology-route scope correction (10 b_1=8 deployments) + cohomology-depth analysis via C3 chain master + `passesCohomologyDepthFilter` (Sym(3) + c=2 binary cover) |
| `DimSpectrum.lean` | 6, 14 | ~14 | Geometrization dim spectrum d_M ∈ {3..6} + Sym(3)-capable enumeration per chartBase |
| `Poincare.lean` | 12, 13, 15 | ~31 | Poincaré pillar (tree characterization + corrected Euler `b1_corrected` + Generalized Poincaré + Filled-cohomology evolution) |
| `Ricci.lean` | 16, 17 | ~9 | Ricci flow pillar via `K32_ricci_modulus` (BracketCauchy parallel) |
| `EightGeometries.lean` | 11, 18-22 | ~30 | 8 model geometries via single Möbius P + 3 Lenses (ℝ, ℤ, F_5).  Includes `all_eight_via_single_mobius_P` + Nil via mod-5 nilpotent (user-derived) |
| `StructuralMapping.lean` | 21, 23, 24 | ~14 | HC_K32 structural hint + universal-8 thesis + ★★★★★★★★★★ ultimate structural mapping (2·trivial → 3 isotropic, 3·standard → 5 anisotropic) |
| `Capstone.lean` | 25 | ~5 | d=4 information richness + ★★★★★★★★★★★ `G121_R1_close_certificate` + master + future-work registry |

## Pillar status (5-pillar Geometrization)

| Pillar | 213-Lens form | Status |
|---|---|---|
| 8 geometries | Möbius P + 3 Lenses (ℝ/ℤ/F_5) ↔ Sym(3) decomp (2·trivial + 3·standard) | ★★★★★★ COMPLETE ✅ |
| JSJ | bipartite S/T cut + Filled cells | PARTIAL ✓ |
| Poincaré | K_{3,1}^{(c=1)} unique tree + S³ = ∂Δ⁴ | DOUBLY REALIZED ✅ |
| Generalized Poincaré | K_{1,k}^{(c=1)} all chartBase | GENERALIZED ✅ |
| Ricci flow | `K32_ricci_modulus` averaging | PARTIAL CLOSE ✅ |

## Open knots (G121 §6)

| Knot | Status |
|---|---|
| M1 (why $d_{213}=5$) | TWO-ROUTE CLOSE (atomicity + Möbius) |
| M2 (chart count = $d-1$) | PARTIAL CLOSE (V32Betti deployment + axiom shadow) |
| M3 (NT axis split) | downstream (physics interpretation) |
| M4 (KK firewall) | doc-level stereotype warnings |

## Future-work marathon candidates (§FW in Capstone.lean)

| ID | Topic | Trigger |
|---|---|---|
| G122 | 4-mfd exotic enumeration via Sym(3) gauge | User-insight 2026-05-22 (exotic 자체 조사) |
| G123 | JSJ deeper close (3-cell complex extension) | §J narrative open since step 11 |
| G124 | K_{NS,NT}^{(c)} generalization | User-deferred at step 17 |
| G125 | E³, H³, H²×ℝ direct realization | Step 20 narrative-only |

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
```

All sub-files share the namespace
`E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz` for
backwards-compatible theorem-name preservation across the
pre-split → post-split refactor.

## Key theorems by file

### Ansatz.lean
  · `chartBase NS NT := NS + NT` (def)
  · `selfPointingAxes : Nat := 1` (def, ansatz commitment)
  · `chartVisibleAxes NS NT := chartBase NS NT - selfPointingAxes`
  · `K32_ansatz_bundle`, `axiom_level_shadow_bundle`
  · `selfPointingAxes_derived_from_K32Betti`
  · `chartVisibleAxes_K32_derived_from_rank_nullity`

### M1Routes.lean
  · `chartBase_K32_derived_from_triangle_iteration`
  · `NS_NT_derived_from_atomicity_two`
  · `M1_cohomology_route_close`
  · `c2_derived_from_mobius_period`
  · `triple_route_K32_c2_unique`

### ScopeAndDepth.lean
  · `cohomology_route_not_unique` (10 b_1=8 deployments)
  · `combined_atomicity_cohomology_uniqueness`
  · `hasNaturalSym3`, `hasC2BinaryCoverMatch`
  · `passesCohomologyDepthFilter`
  · ★★★ `cohomology_depth_uniqueness` (10-conjunct)
  · ★★★★ `strong_combined_uniqueness_with_depth`

### DimSpectrum.lean
  · `dim_spectrum_dM3/4/5/6_*` (per-chartBase analysis)
  · ★★★ `geometrization_spectrum_capstone`
  · `sym3_capable_chartBase_4/5/6/7`
  · ★★★★ `K32_c2_unique_triple_intersection`

### Poincare.lean
  · `isTreeDeployment` (def)
  · `b1_corrected` (corrected Euler formula)
  · ★★★ `Poincare_analog_chartBase_4`
  · ★★★ `regime_transition_corrected`
  · ★★★★ `geometrization_spectrum_with_corrected_euler`
  · ★★★★★ `geometrization_correspondence_capstone`
  · `generalized_Poincare_chartBase_2_to_6`
  · ★★★★ `chartBase_5_tree_and_critical_coexist`
  · ★★★★ `filling_versus_tree_dual_path`

### Ricci.lean
  · `K32_ricci_modulus` (def)
  · `K32_ricci_modulus_reachable/unreachable/monotone`
  · ★★★★ `ricci_modulus_bracket_cauchy_parallel`
  · ★★★★★ `narrative_deepening_completion` (14-conjunct)

### EightGeometries.lean
  · S³ = ∂Δ⁴: `S3_realized_at_boundary_of_delta_4`,
    `G_pillar_S3_partial_close`
  · S² = ∂Δ³: `chi_S2_boundary_via_delta_3`,
    `S2_partial_via_delta_3_boundary`
  · Sol/~SL₂: `Sol_narrative_spiral_at_atomicity`,
    `SL2R_narrative_via_mobius`
  · H²/H³/E³: `hyperbolic_narrative_via_P_trace`,
    `E3_narrative_via_OneAsGlue`
  · Nil (user-derived): `mobius_N_squared_mod_5_zero`,
    `char_poly_collapses_mod_5`, ★★★★★ `Nil_via_mobius_mod_5_complete`
  · ★★★★ `eight_geometries_score` / `eight_geometries_final_scoreboard`
  · ★★★★★★ `all_eight_via_single_mobius_P` (9-conjunct)

### StructuralMapping.lean
  · `K32_eight_classes_hodge_closed` (HC213 invoke)
  · `K32_H1_256_classes`
  · ★★★★★ `geometries_classes_structural_hint`
  · `universal_eight_via_multiple_routes`
  · ★★★★★★★ `operation_closure_universal_eight_capstone`
  · `isotropic_geometry_count := 3`, `anisotropic_geometry_count := 5`
  · ★★★★ `isotropic_three_via_2_trivial`
  · ★★★★ `anisotropic_five_via_3_standard`
  · ★★★★★★★★ `geometrization_8_via_sym3_decomp_structural`
  · ★★★★★ `three_dim_confinement_forces_eight`
  · ★★★★★★★★★★ `G121_ultimate_capstone` (13-conjunct)

### Capstone.lean
  · `dim4_information_richness` (user-insight Lean-anchor)
  · ★★★★★★★★★★★ `G121_R1_close_certificate` (20-conjunct)
  · ★★★★★ `G121_R1_master_capstone`
