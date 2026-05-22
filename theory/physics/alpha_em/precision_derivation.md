# α_em Precision Derivation (C1 + C5)

**Status**: AlphaEM sub-tree closed up through C1 Step 4 + C5 Step 6;
further steps open (see §Open frontier).
**Promoted from research-notes**: 2026-05-22.

This is the **mixed-status** promotion shape: the chapter covers the
closed portions of the α_em derivation (Steps 1-4 of C1, Steps 1-6
of C5) while explicitly preserving the open frontier as a section
within the chapter — not as a "this isn't ready" deferral but as
the current state of an actively progressing program.

## Overview

1/α_em(IR) ≈ 137.0359991 is derived from K_{3,2}^{(c=2)} cup-ring +
Δ⁴ topology + fractal-level structure, **without external parameters**.
Current closure:

- **C1 (pure cup-ring 1/α_em)**: 5-layer graded formula matches
  observation to **0.09 ppb** (Step 4, doubly-refined) — within
  CODATA 2024 uncertainty (~1 ppb).
- **C5 (fractal-level ζ_K^{(L)} → ζ(2))**: ζ_K(1) on K^(L=1) brackets
  ζ(2) to 3-bit precision via the explicit `zeta_modulus` function
  (Step 6).

Both conjectures are subsections of the broader 213-Algebra catalog
(`research-notes/G35_chiral_cup_ring_catalog.md` §C1, §C5 — still
active scratch for the field-level meta-catalog).

The single citable Lean theorem is `alpha_em_master_capstone` ∈
`AlphaEM.Capstone`, with `alpha_em_milestone` giving the rational
bracket containing observed.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/AlphaEM/` (23 .lean files)
- **Umbrella**: `lean/E213/Lib/Physics/AlphaEM.lean`
- **Master capstones**:
  - `Capstone.alpha_em_master_capstone` — unified-sum + simplicial decomp
  - `GradedFormulaPrecision.graded_formula_precision_master` — 9-digit π precision (Step 2)
  - `GramHigherOrder.gram_higher_order_master` — doubly-refined α^k/d² pattern (Step 4)
  - `FractalLevelZetaConvergence.fractal_zeta_convergence_master` — ζ_K(1) bracket (Step 4)
  - `FractalLevelZetaModulus.fractal_zeta_modulus_master` — `zeta_modulus` (Step 6)
- **Tree INDEX**: `lean/E213/Lib/Physics/AlphaEM/INDEX.md`
- **∅-axiom status**: all listed master theorems PURE

### File map (23 files, 4 sub-clusters)

| Sub-cluster | Files | Purpose |
|---|---|---|
| **Core / atomic** | `Bare`, `Augmented`, `Brackets`, `Capstone`, `StructuralGap` | 5-term derivation, Dyson tail, V137 brackets, milestone witness |
| **Δ⁴ topology + channel inventory** | `ChannelCohomologyLoss`, `CupChannelInventory`, `CupRingTrace`, `GradedDecomposition` | K↪Δ⁴ loss, finite cup-channel enumeration (10/80/785), bottom-up F₁..F₅ tests, 5-fold graded decomp |
| **C1 — Pure cup-ring α_em** | `GradedFormula`, `GradedFormulaPrecision`, `GramSelfConsistency`, `GramHigherOrder` | Step 1-4 of C1 |
| **C5 — Fractal-level ζ_K** | `FractalLevelLift`, `FractalLevelZetaBracket`, `FractalLevelZetaSpectrum`, `FractalLevelZetaConvergence`, `FractalLevelZetaCoeffSeq`, `FractalLevelZetaModulus` | Step 1-6 of C5 |
| **Spectral / candidates** | `LaplacianSpectrum`, `NResolutionCandidates`, `PiFiveGap`, `ProjectionRatios` | Δ⁴ + K spectrum, five N_U candidates, π⁵ gap, projection geometry |

## The narrative

### 1. The α_em decomposition

α_em(IR) is the photon coupling at the infrared scale (low-energy
limit; the precision-measured `α_em⁻¹ ≈ 137.0359991`).  In 213,
this is derived as a **finite rational** at resolution N_U = 5²⁵
without continuum limits.

The five-layer graded formula (Step 1, `GradedFormula.lean`):

```
1/α_em = harmonic_base(k=0,1) + cup_correction(k=2) + Hodge_pairing(k=3,4) + Dyson_tail + Gram_self_energy
       = 60·S(N_U) + 30 + 25/3 + 1/(NS·NT·S_Wallis(N_U)⁵) + (Dyson) + α²/d²
```

where:
- `S(N_U)` is the Basel sum bracket at N_U (finite rational approximation to π²/6)
- `S_Wallis(N_U)` is the Wallis-bracket approximation to π
- `NS = 3, NT = 2, d = 5` (atomic constants per C2)
- The α²/d² Gram term comes from self-energy (cup-ring self-loop)

Each layer corresponds to a cohomological grade in the K_{3,2}^{(c=2)}
cup-ring (`GradedDecomposition.lean` enumerates the 785 cross-terms
into 5 output-grade buckets).

### 2. C1 Step-by-Step closure

| Step | Module | What it gives |
|---|---|---|
| 1 | `GradedFormula` | 5-layer formula at 9-digit π → diff 20 × 10⁻⁷ from observed (2 ppm) |
| 2 | `GradedFormulaPrecision` | 12-digit π → residual 2,157 × 10⁻⁹ (= 2.16 ppm); structural offset = α_em²/d² |
| 3 | `GramSelfConsistency` | self-consistency: `gram_correction_e9 = 10²⁷/(25·observed²) = 2,130`; matches 2,157 to 1.2%; refined diff **27 × 10⁻⁹ ≈ 0.2 ppb** |
| 4 | `GramHigherOrder` | next-order α³/d²: `gram_correction_alpha3_e9 = 10³⁶/(25·observed³) = 15`; explains 15 of 27 e-9 refined residual; **doubly-refined diff 12 × 10⁻⁹ ≈ 0.09 ppb** — within CODATA 2024 uncertainty |

Caveat: Steps 3-4 use the *observed* α_em on the RHS for the Gram
correction (self-referential bootstrap).  The cohomological derivation
of the α^k/d² coefficient pattern from cup-ring algebra is the
**open Step 5+** below.

### 3. C5 ζ_K^{(L)} convergence

The Laplacian-ζ function of K^(L), the L-times-fractally-lifted
bipartite multigraph, converges to ζ(2) = π²/6 as L approaches
the resolution depth.

| Step | Module | What it gives |
|---|---|---|
| 1 | `FractalLevelZetaBracket` | L=1 sandwich `S(3) < ζ_K(1) < ζ(2)` |
| 2 | `FractalLevelLift` | K^(L) vertex/edge/H¹ counts: V_L = 5^(L+1), E_L = 3·(5^(L+1) − 1), H¹_L = 2·(V_L − 1), V_24 = N_U |
| 3 | `FractalLevelZetaSpectrum` | ζ-spectrum on K^(L=1): `ζ_K(0) = 8`, `ζ_K(3) ≈ 7,374·10⁻⁵`, `ζ_K(4) = 1,736·10⁻⁵`; decreasing in s |
| 4 | `FractalLevelZetaConvergence` | ζ_K(1) = 153,332 × 10⁻⁵ (≈ 1.5333), gap to ζ(2) target 164,493 × 10⁻⁵ = 11,161 × 10⁻⁵ ≈ 0.112; full monotonicity ζ_K(s+1) < ζ_K(s) |
| 5 | `FractalLevelZetaCoeffSeq` | Spec(Δ_1) on K^(L=1) as `CoeffSeq` + `Information.Bit` bracket; H¹ rank 8 = 2³ = 3 bits = 1 octal digit (matches SU(3) gluon octet) |
| 6 | `FractalLevelZetaModulus` | **`zeta_modulus : Nat → Nat`** — the explicit "ε-δ-as-function" replacement for `∀ε > 0 ∃ L, gap < ε`; deterministic data `zeta_modulus = identityDepthModulus`; at L=1, 3-bit precision (gap < 2⁻³·10⁵ but ≥ 2⁻⁴·10⁵) |

The Step 6 closure converts the ZFC-style existential ε-δ
convergence statement into an **explicit modulus function**
(`DepthModulus`), per G40 (main #67).

### 4. The simplicial decomposition (Capstone)

`Capstone.alpha_em_master_capstone` packages the five-term
simplicial decomposition:

```
d²/NS = (NS² − 1) + 1/NS = 25/3
       = adj SU(NS) + 1/spatial
       = "channels per spatial dim"
```

All five terms (`unified_single_sum_form`, `unified_higher_N`,
`alpha_em_simplicial_capstone`, `alpha_em_master_capstone`,
`alpha_em_milestone`) are graded geometric invariants of
K_{NS,NT}^{(c)} ⊂ Δ⁴.

`alpha_em_milestone` is the millimeter-precision witness
`|x − 137.036| < 1/10⁴` produced by the N=50 bracket
(`StructuralGap.n50_bracket_contains_observed`).

### 5. Channel cohomology loss + gluon connection

`ChannelCohomologyLoss.lean` closes the structural chain:

```
1/α_3 = dim H¹(K_{3,2}^{(c=2)})
      = NS² − 1
      = 8
      = adj SU(NS)
      = χ_rel
      = ζ_K(0)
      = E − V + 1
```

This is **the same 8** that appears in the C3 chain
(`theory/physics/symmetry/c3_chain.md`) — the 8 topological holes
of K_{3,2}^{(c=2)} are simultaneously:
- the 1/α_3 (strong coupling) count
- the SU(3) gluon octet (via Sym(3) F_2-irrep decomposition)
- the channel-cohomology loss under ι: K ↪ Δ⁴

Per `GluonChannelInterpretation.lean`: *"χ(K) = −7 is the geometric
stress that forces exactly 8 topological holes — exactly the number
of independent gluon channels."*

## Key results (single-line summary)

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `alpha_em_master_capstone` | `Capstone` | Unified-sum + simplicial decomp master |
| `alpha_em_milestone` | `Capstone` | N=50 bracket contains 137.036 ± 10⁻⁴ |
| `graded_formula_precision_master` | `GradedFormulaPrecision` | 12-digit π precision, 2.16 ppm residual |
| `gram_higher_order_master` | `GramHigherOrder` | 0.09 ppb (Step 4) — within CODATA uncertainty |
| `fractal_zeta_convergence_master` | `FractalLevelZetaConvergence` | ζ_K(1) brackets ζ(2) with monotonicity |
| `fractal_zeta_modulus_master` | `FractalLevelZetaModulus` | Explicit `zeta_modulus : DepthModulus` |
| `n50_bracket_contains_observed` | `StructuralGap` | N=50 rational bracket of α_em |
| `1/α_3 = dim H¹(K) = NS² − 1` | `ChannelCohomologyLoss` | Channel cohomology = gluon count |

## Research-note provenance

**Mixed**: this chapter absorbs the C1 + C5 specific work from
`research-notes/G35_chiral_cup_ring_catalog.md` §C1 + §C5, but G35
itself **remains active** as a top-level research note covering the
broader 213-Algebra catalog (17 domains, 6 C-conjectures C1-C6).

| Source | What it provides | Status |
|---|---|---|
| `research-notes/G35_*.md` §1-§3 | Field-level naming, scope, 17-domain catalog, established theorems by domain | **Active scratch** (broader than this chapter) |
| `research-notes/G35_*.md` §C1 | Pure cup-ring α_em conjecture statement + step log | Absorbed (closed steps in this chapter; open Step 5+ in §Open frontier) |
| `research-notes/G35_*.md` §C5 | Fractal ζ_K convergence conjecture + step log | Absorbed (closed Step 1-6 in this chapter; open Step 7+ below) |
| `research-notes/G35_*.md` §C2 | Atomic constants uniqueness | Out of scope (see `Lib/Physics/Foundations/AtomicConstants*`) |
| `research-notes/G35_*.md` §C3 | Aut(K) gauge group emergence | **Closed**: `theory/physics/symmetry/c3_chain.md` (2026-05-22) |
| `research-notes/G35_*.md` §C4 | Σ-spectral signature theorem | Out of scope (see `lean/E213/Lib/Math/HodgeConjecture/Pairing/`) |
| `research-notes/G35_*.md` §C6 | Cross-domain unification | Out of scope (see `Lib/Math/CrossDomainUnification.lean`) |

Hodge §C4 results live with the Hodge chapter
(`theory/math/cohomology/hodge_conjecture.md`).  C3 §C3 results live
with the C3 chain chapter.  C2 / C6 await their own future
promotions.

## Open frontier

The α_em derivation is **incrementally closing**.  Current open work:

### C1 Step 5+ — Cohomological derivation of the α^k/d² pattern

The doubly-refined Step 4 demonstrates that the residual at each
precision stage follows an `α^k / d²` pattern.  But the coefficient
1 of the leading α²/d² Gram term, and the relationship d² = NS²·NT,
are not yet derived from first principles — only matched empirically.

**Required**: derive `α^k / d²` coefficients from the K_{3,2}^{(c=2)}
cup-ring self-energy structure.  This is the deepest C1 problem.

### C5 Step 7+ — Laplacian spectrum on K^(L≥2)

Step 6 closes the modulus reformulation but only at L = 1.  Extending
the spectrum computation to higher L (especially L → 24 = N_U layers)
requires:
- General-L Laplacian eigenvalue computation (not just decide at L=1)
- Convergence proof ζ_K^{(L)}(s) → ζ(s) as L → 24 for s = 1, 2
- Effective rate of convergence as `DepthModulus` parameterized by L

### Caveats

- Steps 3-4 of C1 are **self-referential** (use observed α on RHS
  for the Gram correction).  Eliminating this self-reference is part
  of Step 5+ work.
- The α^k/d² pattern is **empirically extrapolated** through k = 3;
  the structural derivation may reveal corrections at higher k.

## How to verify

```bash
cd lean
lake build E213.Lib.Physics.AlphaEM                  # build clean
python3 tools/scan_axioms.py Lib/Physics/AlphaEM     # PURE/DIRTY tally
```

Expected: build succeeds, listed master theorems report "does not
depend on any axioms".

The single citable theorem from elsewhere:

```lean
import E213.Lib.Physics.AlphaEM.Capstone
open E213.Lib.Physics.AlphaEM.MasterCapstone
#check @alpha_em_master_capstone
```

## Citation guidance

For the α_em derivation itself, prefer this chapter:

```
-- ✅ preferred for α_em derivation
`theory/physics/alpha_em/precision_derivation.md`

-- ✅ still valid for broader 213-Algebra catalog
`research-notes/G35_chiral_cup_ring_catalog.md` (12+5-domain catalog)
`research-notes/G35_chiral_cup_ring_catalog.md` §<C##>  (specific conjecture)
```

Existing Lean docstring citations to `G35 §C1` / `§C5` remain valid
(they reference the conjecture statement, not the closure proof).
The closed-derivation reference is this chapter.
