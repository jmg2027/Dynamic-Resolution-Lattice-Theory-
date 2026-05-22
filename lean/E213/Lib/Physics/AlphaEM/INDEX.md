# `Lib/Physics/AlphaEM/` — 1/α_em derivation cluster

1/α_em (≈ 137.0359991) derivation from K_{3,2}^{(c=2)} cup-ring +
Δ⁴ topology + fractal level structure.

**Narrative**: `theory/physics/alpha_em/precision_derivation.md`
(promoted 2026-05-22; covers C1 Steps 1-4 + C5 Steps 1-6 + open
frontier).

The cluster is organised around two `research-notes/G35` conjectures:
  - **C1** — pure cup-ring 1/α_em formula (no SO(10), no Dyson)
  - **C5** — fractal-level ζ_K^{(L)} → ζ(2) convergence

## Files (23)

### Core / atomic
  - `Bare.lean`                    — atomic integers + lattice
                                     prefactors + 5-term derivation
  - `Augmented.lean`               — Dyson tail + SO(10) + Gram
                                     self-energy bracket
  - `Brackets.lean`                — bare / tight / V137 rational
                                     brackets
  - `Capstone.lean`                — unified-sum + simplicial
                                     decomp + master statement
  - `StructuralGap.lean`           — open 5.4×10⁻⁴ falsifier target

### Δ⁴ topology + channel inventory
  - `ChannelCohomologyLoss.lean`   — K↪Δ⁴ topological loss
                                     1/α_3 = NS²−1 = 8 = dim H¹(K)
                                     = χ_rel = ζ_K(0) = E−V+1
  - `CupChannelInventory.lean`     — Δ⁴ cup-channel finite
                                     enumeration (10 / 80 / 785)
  - `CupRingTrace.lean`            — bottom-up cup-ring functional
                                     tests F₁..F₅
  - `GradedDecomposition.lean`     — 5-fold output-grade decomp
                                     of 785 cross-terms

### C1 — Pure cup-ring α_em
  - `GradedFormula.lean`           — Step 1: 5-layer graded formula
  - `GradedFormulaPrecision.lean`  — Step 2: 9-digit π precision
  - `GramSelfConsistency.lean`     — Step 3: α²/d² Gram self-energy
  - `GramHigherOrder.lean`         — Step 4: higher-order Gram

### C5 — Fractal level ζ_K^{(L)}
  - `FractalLevelLift.lean`        — Step 2: K^{(L)} vertex/edge counts
  - `FractalLevelZetaBracket.lean` — Step 1: ζ_K bracket setup
  - `FractalLevelZetaSpectrum.lean`— Step 3: ζ_K(s) for s∈{0..4}
  - `FractalLevelZetaConvergence.lean` — Step 4: |ζ_K^{(1)}(1)−ζ(2)|
  - `FractalLevelZetaCoeffSeq.lean`— Step 5: spectrum as CoeffSeq
  - `FractalLevelZetaModulus.lean` — Step 6: convergence modulus

### Spectral / candidates
  - `LaplacianSpectrum.lean`       — Δ⁴ + K spectrum finite ζ
  - `NResolutionCandidates.lean`     — five N_U candidates
  - `PiFiveGap.lean`               — π⁵ structural-gap conjecture
  - `ProjectionRatios.lean`        — K_{3,2} ↔ Δ⁴ projection geom

## Top-level

  - `AlphaEM.lean` — aggregator (imports all 23 files)

## Axiom status

Strict ∅-axiom on `ChannelCohomologyLoss`, `GradedDecomposition`,
`LaplacianSpectrum`, `PiFiveGap`, `ProjectionRatios` (per file
header).  Other files may carry decidability dependencies.

## Connection to other clusters

  - `Lib/Physics/Couplings/AlphaGUT`            — α_GUT ⇒ α_em(IR) at low scale
  - `Lib/Math/Cohomology/CupAW`                 — Alexander-Whitney cup product
  - `Lib/Physics/Symmetry/`                     — C3 chain (gluon octet from H¹(K))
  - `theory/physics/alpha_em/precision_derivation.md` — narrative
  - `research-notes/G35_chiral_cup_ring_catalog.md`   — broader 213-Algebra catalog (active scratch)

## Where to add new α_em-related files

  - C1 cup-ring step    → `GradedFormula*`, `Gram*`
  - C5 fractal step     → `FractalLevel*`
  - New topology layer  → `Channel*`, `Cup*`
  - New conjecture step → match existing `Step N` naming
