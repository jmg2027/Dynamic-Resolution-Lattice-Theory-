# GeometrizationConjecture — sub-tree INDEX

213-Lens reading of the Thurston/Perelman Geometrization conjecture
and the dimension-4 exotic-smoothness anomaly.

**Status**:
  · **G121 R1 CLOSED** at ~149 PURE / 0 DIRTY across 25 steps (2026-05-22)
  · **G121 R1+ PARTIAL** for G123/G124/G125 (2026-05-22 extension)

Cross-reference: `research-notes/G121_dim4_self_pointing_axis.md`.

## File map

### Core (G121 R1, CLOSED)

| File | Steps | PURE | Content |
|---|---|---|---|
| `Ansatz.lean` | 1-3 | ~23 | Core defs (`chartBase`, `selfPointingAxes`, `chartVisibleAxes`) + axiom-level shadow + V32Betti deployment |
| `M1Routes.lean` | 4, 5, 8 | ~7 | M1 atomicity + cohomology route + c=2 Möbius forcing |
| `ScopeAndDepth.lean` | 7, 9, 10 | ~28 | Cohomology-route scope correction + depth filter (Sym(3) + c=2 binary cover) |
| `DimSpectrum.lean` | 6, 14 | ~14 | Geometrization dim spectrum d_M ∈ {3..6} + Sym(3)-capable enumeration |
| `Poincare.lean` | 12, 13, 15 | ~31 | Poincaré pillar (tree + corrected Euler + Generalized + Filled) |
| `Ricci.lean` | 16, 17 | ~9 | Ricci modulus (BracketCauchy parallel) |
| `EightGeometries.lean` | 11, 18-22 | ~30 | 8 model geometries via single Möbius P + 3 Lenses (ℝ/ℤ/F_5) |
| `StructuralMapping.lean` | 21, 23, 24 | ~14 | HC_K32 + universal-8 + ★★★★★★★★★★ ultimate structural mapping |
| `Capstone.lean` | 25 | ~5 | d=4 info richness + ★★★★★★★★★★★ `G121_R1_close_certificate` |

### R1+ Extensions (G123/G124/G125 partials)

| File | Target | PURE | Content |
|---|---|---|---|
| `Generalization.lean` | G124 | ~7 | K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended: tree enumeration + cohomology-depth uniqueness extended range |
| `JsjDeep.lean` | G123 | ~6 | JSJ 3-cell complex Euler-target scaffold: χ-targets for closed 3-mfds + sphere Euler via ∂Δⁿ |
| `MetricGeometries.lean` | G125 | ~7 | E³/H³/H²×ℝ via mod-k Möbius P Lens family (F_2 / F_3 / F_5 / F_7 / F_11) |

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
```

Linear chain (each file imports previous one).
All under namespace `E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz`.

## Open knots (G121 §6)

| Knot | Status |
|---|---|
| M1 (why $d_{213}=5$) | TWO-ROUTE CLOSE (atomicity + Möbius) |
| M2 (chart count = $d-1$) | PARTIAL CLOSE (V32Betti + axiom shadow) |
| M3 (NT axis split) | downstream (physics interpretation) |
| M4 (KK firewall) | doc-level stereotype warnings |
