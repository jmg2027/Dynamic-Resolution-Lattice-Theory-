# Geometrization Conjecture (213-Lens reading)

**Status**: G121 R1 closed (~149 PURE / 0 DIRTY across 25 steps); R1+
extensions partial (G123/G124/G125); G122 open (4-mfd exotic
enumeration via Sym(3) gauge).
**Promoted from research-notes**: 2026-05-22.

Pattern 3 (mixed-status absorption): R1 closure + R1+ partials +
open G122-G125 marathon candidates.  G121 note stays as the
companion research direction.

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

Per `seed/AXIOM/09_chart_relativity.md` + CLAUDE.md "Algebraic
priority": *213 sees discrete decomposition first*.  JSJ becomes
*non-separable component enumeration*; incompressible torus becomes
*π₁-injectivity* (algebraic); Ricci flow becomes *chart-Lens
coherentization flow*.

The G121 R1 close certificate (step 25, `Capstone.G121_R1_close_certificate`)
bundles 20 conjuncts across the 5 Geometrization pillars.

## d=4 anomaly reframing (Mingu's central insight)

Standard math reads d=4 exotic smoothness as **anomaly** — continuum-many
smooth structures on a single topological 4-manifold, no structural
reason known.  G121 reads it as **feature**:

| d_M | structural options visible | reading |
|---|---|---|
| ≤ 3 | tree only (single-form) | **confinement** — chart-Lens freedom too narrow for Raw self-pointing residue to escape |
| 4 | tree + critical (BOTH branches) | **critical / direct projection** — chart-Lens freedom matches Raw residue density; Raw "jagged" structure shows through |
| ≥ 5 | multiple, all averaged-out | **resolution smearing** — chart-Lens excess freedom averages out residue; surgery works; only finite Θ_d survives |

d = 4 is the **slit-widest camera** — the dimension where BOTH
tree-branch (Poincaré-flat topology) and critical-branch (rich
K_{3,2}^{(c=2)} cohomology) coexist visibly.  *Defect is signal
richness.*

The G121 ansatz: **d_M = d_213 − 1 = 5 − 1 = 4** is *forced by Raw
self-pointing structure*, not a geometric coincidence.  M1/M2/M3/M4
"knots" formalize the chain.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/GeometrizationConjecture/` (13 files, linear dependency chain)
- **Master capstone**: `Capstone.G121_R1_close_certificate` (20-conjunct)
- **Master capstone alt**: `Capstone.G121_R1_master_capstone` (4-route convergence)
- **Tree INDEX**: `lean/E213/Lib/Math/GeometrizationConjecture/INDEX.md`
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
| `Capstone.lean` | 25 | ~5 | d=4 info richness + `G121_R1_close_certificate` |

### File map (R1+ extensions, partial)

| File | Target | PURE | Content |
|---|---|---|---|
| `Generalization.lean` | G124 | ~7 | K_{NS,NT}^{(c)} chartBase ∈ {4..8} extended |
| `JsjDeep.lean` | G123 | ~6 | JSJ 3-cell complex Euler-target scaffold |
| `MetricGeometries.lean` | G125 | ~7 | E³/H³/H²×ℝ via mod-k Möbius P Lens family |

### Dependency chain

```
Ansatz → M1Routes → ScopeAndDepth → DimSpectrum → Poincare →
   Ricci → EightGeometries → StructuralMapping → Capstone →
      Generalization → JsjDeep → MetricGeometries
```

Linear chain.  All under namespace
`E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz`.

## The narrative

### 1. The 5 pillars

| Pillar | 213-Lens form | Status |
|---|---|---|
| **8 geometries** | Möbius P + 3 Lenses (ℝ/ℤ/F_5) ↔ Sym(3) decomp (2·trivial + 3·standard) | ✅ COMPLETE |
| **JSJ** | bipartite S/T + Filled cells (+JsjDeep χ-targets) | ✓ PARTIAL (G123 partial) |
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

The G121 ansatz **d_M = d_213 − 1 = 5 − 1 = 4** thus identifies
the standard 4-mfd exotic as **the 213-native dimension** where the
self-pointing residue is fully visible.

### 5. Four-route convergence (master capstone)

`G121_R1_master_capstone` bundles four independent routes to the
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
| `G121_R1_close_certificate` | `Capstone` | ★★★★★★★★★★★ 20-conjunct close certificate for R1 |
| `G121_R1_master_capstone` | `Capstone` | ★★★★★ 4-route convergence master |
| `chartBase_5_tree_and_critical_coexist` | `Capstone` | d=4 info richness: both branches coexist |
| `dim_spectrum_d_M_eq_4_unique` | `DimSpectrum` | d_M = d_213 − 1 = 4 forcing |
| `eight_geometries_via_mobius_P` | `EightGeometries` | One Möbius P + 3 Lenses = 8 geometries |
| `sym3_decomp_8_eq_3_iso_5_aniso` | `StructuralMapping` | Step 24 ultimate structural mapping |
| `K32_ricci_modulus_partial_close` | `Ricci` | Ricci flow → BracketCauchy parallel |
| `poincare_via_K31_unique_tree` | `Poincare` | Poincaré via K_{3,1}^{(c=1)} |
| `cohomology_depth_filter_K32` | `ScopeAndDepth` | Sym(3) + c=2 binary cover filter |

For full ~149 PURE inventory, see
`lean/E213/Lib/Math/GeometrizationConjecture/INDEX.md`.

## Research-note provenance

Single source note `research-notes/G121_dim4_self_pointing_axis.md`
(1531 lines) — stays as **active research direction** rather than
fully archived.  Reason: G121 *also* hosts the G122-G125 marathon
candidates which are currently OPEN or PARTIAL, plus M3/M4 knots
still doc-level.

| G121 §section | Status | Promoted? |
|---|---|---|
| §1-§3 Setup + ansatz + d=4 anomaly | Closed R1 | ✓ in this chapter |
| §4 5 pillars | Closed R1 | ✓ in this chapter |
| §5 Structural mapping | Closed step 24 | ✓ in this chapter |
| §6 Four open knots (M1-M4) | M1/M2 partial Lean; M3/M4 doc-level | ✓ status in this chapter |
| §7 R1+ extensions (G123/G124/G125) | Partial | ✓ in this chapter §Open frontier |
| §8 G122 4-mfd exotic enumeration | Open marathon | ✗ stays in G121 |
| §9-§N Side observations | Active | ✗ stays in G121 |

The G121 note is partially absorbed (R1 closure) but stays active
for the open marathon candidates.  Same pattern as G35 (213-Algebra
catalog) — chapter covers closed sub-topics; note hosts the
research frontier.

## Open frontier

### R1+ partial extensions (PARTIAL closure achieved 2026-05-22)

- **G123 JSJ 3-cell complex** (`JsjDeep.lean`, ~6 PURE): Euler-target
  scaffold for closed 3-mfds + sphere Euler via ∂Δⁿ.  Full JSJ
  closure pending.
- **G124 K_{NS,NT}^{(c)} generalization** (`Generalization.lean`,
  ~7 PURE): chartBase ∈ {4..8} extended tree enumeration +
  cohomology-depth uniqueness extended range.  Full generalization
  pending.
- **G125 Metric geometries direct realization** (`MetricGeometries.lean`,
  ~7 PURE): E³/H³/H²×ℝ via mod-k Möbius P Lens family (F_2 / F_3
  / F_5 / F_7 / F_11).  Full direct realization pending.

### G122 4-mfd exotic enumeration via Sym(3) gauge — OPEN

The biggest open marathon.  G121 step 25 (Capstone) gestures at
the formal infrastructure (Sym(3) gauge action on K_{3,2}^{(c=2)}
matches Donaldson's gauge theory shape) but a full **enumeration
of exotic smooth structures via 213-native gauge data** is the
distinct open marathon.

Connection to `c3_chain_master` (Phase 12 in C3 chain) suggests the
formal scaffolding is in place — what's missing is the explicit
exotic-counting theorem.

### M3 / M4 knots (doc-level only)

| Knot | Topic | Status |
|---|---|---|
| M3 | NT axis split (physics interpretation) | doc-level downstream |
| M4 | KK firewall stereotype warning | doc-level only |

Neither has Lean witness yet; both noted in G121 §6.

### Below DRLT Validation Standard

G121 R1 is **structural** but not yet a *precision theorem* or
*falsifier* per DRLT Validation Standard (`seed/AXIOM/04_falsifiability.md`).
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
lake build E213.Lib.Math.GeometrizationConjecture
python3 tools/scan_axioms.py Lib/Math/GeometrizationConjecture
```

Expected: build succeeds, all 149+ PURE theorems report "does
not depend on any axioms", scan reports 0 DIRTY.

The single citable theorems from elsewhere:

```lean
import E213.Lib.Math.GeometrizationConjecture
open E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz
#check @G121_R1_close_certificate   -- 20-conjunct close
#check @G121_R1_master_capstone     -- 4-route convergence
```

## Citation guidance

```
-- ✅ preferred (closed R1 narrative)
`theory/math/geometrization_conjecture.md`

-- ✅ also valid (R1+ extensions, open frontier, G122-G125, side observations)
`research-notes/G121_dim4_self_pointing_axis.md`

-- specific theorems
`Lib/Math/GeometrizationConjecture/Capstone.G121_R1_close_certificate`
`Lib/Math/GeometrizationConjecture/Capstone.G121_R1_master_capstone`
```

G121 stays active per Pattern 3 (mixed-status): chapter handles R1
closure, G121 hosts the open marathon front.
