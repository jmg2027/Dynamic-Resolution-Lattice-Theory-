# Geometrization Conjecture (213-Lens reading)

**Status**: R1 closed (~149 PURE / 0 DIRTY across 25 steps) plus
R1+ deepenings: FW-2 (JSJ extension + concrete 3-mfd attaching +
L(p, q) parameter family + classification refinement + connected
sum + universal preservation + multi-fold + Heegaard genus +
additivity + lens invariants), FW-4 (metric direct + geometric
structure cross-frame), I-3 (Ricci ε-Lens), and 8-geo Lie group
infrastructure — adding ~231 PURE.  Sub-tree total: ~380 PURE / 0 DIRTY.

## Overview

Thurston/Perelman's Geometrization conjecture states every closed
orientable 3-manifold admits a canonical decomposition (prime + JSJ)
where each piece carries one of 8 homogeneous geometries.  The
213-Lens reading recasts this as:

```
"manifold" = global coherence of chart-Lens self-pointing
"3-dim" = count-Lens readout of independent chart freedoms
"8 geometries" = algebraic enumeration of 3-dim Lie groups
                 with transitive action + compact isotropy
                 (a COUNTING result, not geometric)
```

Per `seed/AXIOM/06_lens_readings.md` + CLAUDE.md "Algebraic
priority": *213 sees discrete decomposition first*.  JSJ becomes
*non-separable component enumeration*; incompressible torus becomes
*π₁-injectivity* (algebraic); Ricci flow becomes *chart-Lens
coherentization flow*.

The R1 close certificate (step 25, `Capstone.R1_close_certificate`)
bundles 20 conjuncts across the 5 Geometrization pillars.

## d=4 anomaly reframing (Mingu's central insight)

Standard math reads d=4 exotic smoothness as **anomaly** — continuum-many
smooth structures on a single topological 4-manifold, no structural
reason known.  The chapter reads it as **feature**:

| d_M | structural options visible | reading |
|---|---|---|
| ≤ 3 | tree only (single-form) | **confinement** — chart-Lens freedom too narrow for Raw self-pointing residue to escape |
| 4 | tree + critical (BOTH branches) | **critical / direct projection** — chart-Lens freedom matches Raw residue density; Raw "jagged" structure shows through |
| ≥ 5 | multiple, all averaged-out | **resolution smearing** — chart-Lens excess freedom averages out residue; surgery works; only finite Θ_d survives |

d = 4 is the **slit-widest camera** — the dimension where BOTH
tree-branch (Poincaré-flat topology) and critical-branch (rich
K_{3,2}^{(c=2)} cohomology) coexist visibly.  *Defect is signal
richness.*

The self-pointing-dim-4 ansatz: **d_M = d_213 − 1 = 5 − 1 = 4** is *forced by Raw
self-pointing structure*, not a geometric coincidence.  M1/M2/M3/M4
"knots" formalize the chain.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Geometry/GeometrizationConjecture/` (15 files, linear dependency chain)
- **Master capstone**: `Capstone.R1_close_certificate` (20-conjunct)
- **Master capstone alt**: `Capstone.R1_master_capstone` (4-route convergence)
- **Tree INDEX**: `lean/E213/Lib/Math/Geometry/GeometrizationConjecture/INDEX.md`
- **∅-axiom status**: 149 PURE / 0 DIRTY (verified at step-25 close)

### File map (R1 core, 9 files closed)

| File | Steps | PURE | Content |
|---|---|---|---|
| `Ansatz.lean` | 1-3 | ~23 | Core defs (`chartBase`, `selfPointingAxes`, `chartVisibleAxes`) + axiom-level shadow + V32Betti deployment |
| `M1Routes.lean` | 4, 5, 8 | ~7 | M1 atomicity + cohomology route + c=2 Möbius forcing |
| `ScopeAndDepth.lean` | 7, 9, 10 | ~28 | Cohomology-route scope correction + depth filter (Sym(3) + c=2 binary cover) |
| `DimSpectrum.lean` | 6, 14 | ~14 | Geometrization dim spectrum d_M ∈ {3..6} + Sym(3)-capable enumeration |
| `Poincare.lean` | 12, 13, 15 | ~31 | Poincaré pillar (tree + corrected Euler + Generalized + Filled) |
| `Ricci.lean` | 16, 17 | ~9 | Ricci modulus (BracketCauchy parallel) |
| `EightGeometries.lean` | 11, 18-22 | ~30 | 8 model geometries via single Möbius P + 3 Lenses (ℝ/ℤ/F_5) |
| `StructuralMapping.lean` | 21, 23, 24 | ~14 | HC_K32 + universal-8 + ultimate structural mapping (Sym(3) decomp = 3 iso + 5 aniso) |
| `Capstone.lean` | 25 | ~5 | d=4 info richness + `R1_close_certificate` |

### File map (R1+ extensions, partial)

| File | Target | PURE | Content |
|---|---|---|---|
| `Generalization.lean` | Real213-p-adic extensions B | ~7 | K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended |
| `JsjDeep.lean` | Real213-p-adic extensions A | ~6 | JSJ 3-cell complex Euler-target scaffold |
| `MetricGeometries.lean` | Real213-p-adic extensions C | ~7 | E³/H³/H²×ℝ via mod-k Möbius P Lens family |

### Dependency chain

```
Ansatz → M1Routes → ScopeAndDepth → DimSpectrum → Poincare →
   Ricci → EightGeometries → StructuralMapping → Capstone →
      Generalization → JsjDeep → MetricGeometries
```

Linear chain.  All under namespace
`E213.Lib.Math.Geometry.GeometrizationConjecture.ChartAxisAnsatz`.

## The narrative

### 1. The 5 pillars

| Pillar | 213-Lens form | Status |
|---|---|---|
| **8 geometries** | Möbius P + 3 Lenses (ℝ/ℤ/F_5) ↔ Sym(3) decomp (2·trivial + 3·standard) | ✅ COMPLETE |
| **JSJ** | bipartite S/T + Filled cells (+JsjDeep χ-targets) | ✓ PARTIAL (Real213-p-adic extensions A partial) |
| **Poincaré** | K_{3,1}^{(c=1)} unique tree + S³ = ∂Δ⁴ | ✅ DOUBLY REALIZED |
| **Generalized Poincaré** | K_{1,k}^{(c=1)} all chartBase | ✅ GENERALIZED |
| **Ricci flow** | `K32_ricci_modulus` averaging | ✅ PARTIAL CLOSE |

### 2. One algebraic source, eight geometries

The deepest finding (step 22, user-derived): all 8 model
geometries arise from **a single algebraic object** — the Möbius
matrix P [[2,1],[1,1]] (per `theory/math/universe_chain.md`
Step 7) — read through **different Lens applications**:

| Modulus / Lens | Polynomial mod p | Geometric narrative |
|---|---|---|
| ℝ | distinct irrational roots | H², H³, Sol |
| ℤ | det = 1 (SL(2,ℤ)) | ~SL₂(ℝ) |
| F_2 | irreducible (x² + x + 1) | E³ candidate (flat) |
| F_3 | irreducible (x² + 1) | H²×ℝ candidate |
| **F_5** | (λ+1)² double root | **Nil** ✅ (user-derived) |
| F_7 | irreducible (5 not square) | H³ candidate |
| F_11 | reducible (4² = 5 mod 11) | split-geometry candidate |

**One algebraic source (Möbius P), seven Lens readings, eight
geometric narratives**.  Step 22 (Mingu): "F_5 Nil via mod-5
nilpotent collapse" — the user-derived insight that crystallized
the unification.

### 3. Sym(3) structural mapping (step 24, ★★★★★★★★★★)

The 8 geometries decompose under the Sym(3) symmetric-group action:

```
8 = 3 isotropic + 5 anisotropic
  = (3 trivial in Sym3IrrepDecomp) + (5 = 2 fixed pairs + 3 standard)
```

Connects to:
- `theory/physics/symmetry/c3_chain.md` — same Sym(3) decomposition of H¹(K_{3,2}^{(c=2)}) = 2 trivial + 3 standard over F_2
- `theory/math/cohomology/hodge_conjecture.md` HC_K32 — same 8-dim cohomology

**Three apparently distinct objects (Geometrization 8 geometries,
gluon octet, K_{3,2}^{(c=2)} cohomology) share the same algebraic
spine: Sym(3) decomposition on an 8-element substrate.**

### 4. d=4 information richness (step 25)

The closing insight that re-reads the d=4 exotic anomaly.  In
standard math: d=4 is *broken* (continuum-many smooth structures
on a topological manifold).  In 213: d=4 is *the only dimension
where Raw self-pointing residue projects directly* without
confinement (d ≤ 3) or smearing (d ≥ 5).

`c3_chain_master` (`theory/physics/symmetry/c3_chain.md`) provides
formal infrastructure: Sym(3) gauge action on K_{3,2}^{(c=2)} edge
structure (|Aut(K)| = 768), same formal layer as standard 4-mfd
gauge theory (Donaldson).  Gluon octet = coker(ι*: H¹(Δ⁴) →
H¹(K_{3,2}^{(c=2)})) = (F_2)^8 — same formal role as instanton
moduli space.

The self-pointing-dim-4 ansatz **d_M = d_213 − 1 = 5 − 1 = 4** thus identifies
the standard 4-mfd exotic as **the 213-native dimension** where the
self-pointing residue is fully visible.

### 5. Four-route convergence (master capstone)

`R1_master_capstone` bundles four independent routes to the
same structural facts:
1. **Atomicity route** (M1 via NS=3, NT=2, d=5 forcing)
2. **Cohomology route** (M1 via K_{3,2}^{(c=2)} H¹ rank 8)
3. **c=2 Möbius route** (M1 via mod-5 closure P^10 ≡ I)
4. **V32Betti deployment route** (M2 axiom-level shadow)

Four independent paths to the same 213-native Geometrization
reading — significant cross-frame convergence.

## Key results

| Theorem | Module | Statement (informal) |
|---|---|---|
| `R1_close_certificate` | `Capstone` | ★★★★★★★★★★★ 20-conjunct close certificate for R1 |
| `R1_master_capstone` | `Capstone` | ★★★★★ 4-route convergence master |
| `chartBase_5_tree_and_critical_coexist` | `Capstone` | d=4 info richness: both branches coexist |
| `dim_spectrum_d_M_eq_4_unique` | `DimSpectrum` | d_M = d_213 − 1 = 4 forcing |
| `eight_geometries_via_mobius_P` | `EightGeometries` | One Möbius P + 3 Lenses = 8 geometries |
| `sym3_decomp_8_eq_3_iso_5_aniso` | `StructuralMapping` | Step 24 ultimate structural mapping |
| `K32_ricci_modulus_partial_close` | `Ricci` | Ricci flow → BracketCauchy parallel |
| `poincare_via_K31_unique_tree` | `Poincare` | Poincaré via K_{3,1}^{(c=1)} |
| `cohomology_depth_filter_K32` | `ScopeAndDepth` | Sym(3) + c=2 binary cover filter |

For full ~149 PURE inventory, see
`lean/E213/Lib/Math/Geometry/GeometrizationConjecture/INDEX.md`.

## Open frontier

### Substantive deepenings (closed via cross-frame extensions)

- **JSJ extension (FW-2)** (`JsjDeep.lean`, ~181 PURE): Euler-target
  scaffold + 3-mfd catalog; cycle inventory (9 atomic / rank 8);
  concrete (k, j) attaching + bipartite S/T → JSJ torus parallel;
  explicit 3-mfd target attaching maps (S³, T³, L(p,q));
  L(p, q) parameter family + classification refinement
  (`lensEquivFull` extending with `q·q'≡±1 (mod p)`); connected sum
  with PURE universal `k - j = 7` preservation (without `omega`);
  **multi-fold connected sums** via `multiConnectedSumShape` folding
  over a list with `(7, 0)` = S³ identity; concrete pair/triple/mixed
  examples; **Heegaard splitting genus** `heegaardGenus` per 3-mfd
  target (S³ → 0, T³ → 3, L(p, q) → 1 universal); additivity
  `heegaardGenusSum`; list-version `multiHeegaardGenus`;
  S³ characterisation `isS3_byGenus` (decidable Poincaré-style test);
  capstones `FW2_concrete_attaching_close`, `Lpq_parameter_family_close`,
  `connectedSum_and_Lpq_refinement_close`, `connectedSum_universal_close`,
  `multi_fold_connected_sum_close`, `heegaard_genus_close`.
- **K_{NS,NT}^{(c)} universal closure** (`Generalization.lean`,
  ~16 PURE): per-chartBase tables extended + **Prop-level
  universal characterization** `sym3_c2_force_K32` (Sym(3) +
  c=2-binary-cover ALONE force {n,m}={2,3} ∧ c=2 across all Nat,
  no chartBase bound) + Boolean ↔ form `passes_filter_universal_bool`
  + asymptotic `filter_passes_only_chartBase_5`.
- **Metric geometries direct realization (FW-4) + 8-geo Lie group
  infra** (`MetricGeometries.lean`, ~40 PURE): mod-k Möbius P Lens
  family across F_2/F_3/F_5/F_7/F_11/F_13 + **F_5 uniqueness**
  (`mod_k_lens_family_F5_unique_close`); plus discrete metric data
  per geometry — **curvature signs** (3 const-curv + Nil-flat
  + 4 mixed), **isometry group dimensions** (6/6/6/4/4/4/4/3 =
  total 37), **Lie group dimensions** (6 at dim 3, 2 at dim 0
  = total 18); **6-class Lie partition** (semisimple S³ + ~SL₂,
  abelian E³, nilpotent Nil, solvable Sol, hyperbolic H³,
  product-mixed S²×ℝ + H²×ℝ); center-dim partition
  (3 + 1 + 1 + 1 + 0·4 = 6); all 8 simply-connected; capstones
  `FW4_direct_realization_close` + `eight_geo_lie_group_infra_close`.
  Bridges to `Geometry/MetricTypes.lean` (16 PURE).
- **Sym(3) cross-frame capstone** (`CrossFrame.lean`, ~5 PURE):
  `X1_sym3_cross_frame_capstone` bundles the 4-way Sym(3)
  convergence (Geometrization + gluon octet + HC_K32 + Möbius P
  mod-5) + `sym3_basis_thurston_mapping` (explicit Sym(3)-irrep
  basis ↔ Thurston geometry assignment with the +1/−1 reshape
  arithmetic translating 2+6 → 3+5).
- **Ricci pillar ε-Lens integration (I-3)** (`Ricci.lean`,
  ~21 PURE): `IsRicciModulus` structure parallel to
  `Topology.Continuity.IsContinuousModulus`; `K32_isRicciModulus`
  instance; full Nat anti-monotonicity; plus
  **fixed-point at b_1 max** (target = 8 ⇒ modulus = 0);
  **saturation** (target ≤ 5 keeps modulus ≥ 3); **bijection** on
  reachable range {5..8} ↔ {0..3}; strict monotonicity; composition
  semantics; `I3_ricci_eps_lens_deepening_close` capstone.
- **Poincaré two-layer reading** (`Poincare.lean`, +1):
  `poincare_two_layer_trivial_loop` via `V32Betti.b0_eq_1` —
  explicit b₀ (connectedness) + b₁ (cycle absence) decomposition
  of "trivial loop residue".

### 4-mfd exotic enumeration via Sym(3) gauge — substantive count

`Exotic4Mfd.lean` (~15 PURE):

- **Atomic gauge invariant**: `sym3GaugeInvariant = 4` (=
  `Sym3IrrepDecomp.fixedSize`, dim 2 trivial-isotypic subspace).
- **Per-element Sym(3) fix counts** (Burnside prerequisites):
  `fixedSizeS01 = 32`, `fixedSizeS12 = 32`, `fixedSizeRho = 4`
  via 256-cochain enumeration + `decide`.
- **`sym3OrbitCount = 60`** — Burnside-derived count of distinct
  Sym(3)-orbits on H¹(K_{3,2}^{(c=2)}):
  `(256 + 3·32 + 2·4) / 6 = 360 / 6 = 60`.
- **`fw1_substantive_sym3_orbit_count`** capstone — the
  213-native gauge-orbit count playing the structural role of
  Donaldson's integer instanton-moduli enumeration.

Decomposition: 4 singleton orbits (Sym(3)-fixed = `ω_00, ω_10,
ω_01, ω_11`) + 56 non-singleton orbits = 60.

**Sub-orbit decomposition** (`fw1_suborbit_decomposition`):
the 60 orbits partition into (4, 0, 28, 28) by orbit size
(1, 2, 3, 6).  The 0 size-2 count is a structural finding:
`|Fix(ρ)| = |Fix(Sym(3))| = 4` means no cochain has stab exactly
equal to A_3 = ⟨ρ⟩.

Still open: signed counting (Donaldson invariants are signed sums)
and standard-math interface for "smooth-structure equivalence".

### M3 / M4 knots (doc-level only)

| Knot | Topic | Status |
|---|---|---|
| M3 | NT axis split (physics interpretation) | doc-level downstream |
| M4 | KK firewall stereotype warning | doc-level only |

Neither has Lean witness yet; both noted in source §6.

### Below DRLT Validation Standard

R1 is **structural** but not yet a *precision theorem* or
*falsifier* per DRLT Validation Standard (`seed/AXIOM/08_falsifiability.md`).
The ansatz d_M = d_213 − 1 is structural; converting to a measurable
falsifier (e.g., "no exotic smooth structures on a specific closed
4-mfd are observable" or similar) is a separate research arc.

## Cross-frame connections

The 8-geometry decomposition (Geometrization) collapses with:
- **C3 chain gauge emergence** (`theory/physics/symmetry/c3_chain.md`):
  same Sym(3) decomposition (2 trivial + 3 standard) on the 8-element
  H¹(K_{3,2}^{(c=2)}) substrate
- **Hodge conjecture HC_K32** (`theory/math/cohomology/hodge_conjecture.md`):
  same 8-class cohomology
- **Universe chain Möbius P** (`theory/math/universe_chain.md`):
  same generator [[2,1],[1,1]] now read through 7 mod-k Lenses
- **Algebra tower asymptote φ** (`theory/math/cayley_dickson/algebra_tower.md`):
  same Möbius signature

→ **Geometrization 8 geometries + gluon octet + K_{3,2}^{(c=2)}
cohomology + Möbius P pentagonal closure** — four 213-native pillars
sharing one algebraic spine.  This convergence is the
"ultimate structural mapping" of step 24.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Geometry.GeometrizationConjecture
python3 tools/scan_axioms.py Lib/Math/Geometry/GeometrizationConjecture
```

Expected: build succeeds, all 149+ PURE theorems report "does
not depend on any axioms", scan reports 0 DIRTY.

The single citable theorems from elsewhere:

```lean
import E213.Lib.Math.Geometry.GeometrizationConjecture
open E213.Lib.Math.Geometry.GeometrizationConjecture.ChartAxisAnsatz
#check @R1_close_certificate          -- 20-conjunct R1 close
#check @R1_master_capstone            -- 4-route M1 convergence
#check @X1_sym3_cross_frame_capstone  -- 4-way Sym(3) cross-frame
#check @sym3_basis_thurston_mapping        -- explicit basis ↔ geometry
#check @sym3_c2_iff_K32_or_K23             -- universal filter closure
#check @passes_filter_universal_bool       -- Boolean ↔ form
#check @poincare_two_layer_trivial_loop    -- b₀ + b₁ Poincaré reading
#check @ricci_eps_lens_full_integration    -- ε-Lens integration
#check @JSJ_deeper_consolidation           -- JSJ-pillar deepening
#check @mod_k_lens_family_F5_unique_close  -- F_5 Nil uniqueness
#check @fw1_substantive_sym3_orbit_count   -- 60 Sym(3)-orbits (Burnside)
#check @fw1_suborbit_decomposition         -- (4, 0, 28, 28) sub-orbit decomp
#check @geometrization_followup_close_certificate  -- 33-conjunct mega-capstone
```

## Citation guidance

```
-- ✅ preferred (closed R1 narrative)
`theory/math/geometrization_conjecture.md`

-- ✅ also valid (R1+ extensions, open frontier, Real213-p-adic research and its extensions, side observations)

-- specific theorems
`Lib/Math/Geometry/GeometrizationConjecture/Capstone.R1_close_certificate`
`Lib/Math/Geometry/GeometrizationConjecture/Capstone.R1_master_capstone`
```

the chapter stays active per Pattern 3 (mixed-status): chapter handles R1
closure, dim-4 self-pointing closure hosts the open marathon front.
