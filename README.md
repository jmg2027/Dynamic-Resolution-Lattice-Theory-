# Dynamic Resolution Lattice Theory (DRLT)

**Author:** Mingu Jeong (Independent Researcher)  
**Co-researcher:** Claude (Anthropic) — mathematical formalization, numerical experiments, code

## The Axiom

> Points exist. Between every pair, there is a relation G_ij = ⟨ψ_i|ψ_j⟩ ∈ ℂ. That is all.

## Derivation Chain

```
Points with relations
  → ℂ is the unique substrate (Frobenius theorem)
  → d = 5 is the unique dimension (atomic uniqueness + swap annihilation)
  → (2,3) is the unique chiral structure (representation-theoretic, for any N)
  → SU(3)×SU(2)×U(1) is the unique gauge group
  → α_GUT = 6/(25π²) is a mathematical theorem
  → Ξ universal correction: α_em/(1-α)+α/(d²-1)+α_em²
  → 60+ physical observables, ZERO free parameters
```

## Key Results (0 free parameters)

| Quantity | DRLT | Observed | Error |
|----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p (proton) | 938.27 MeV | 938.27 MeV | **0.000%** |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.7 ppb** |
| m_τ/m_μ | 16.8169 | 16.8170 | **5 ppm** |
| η_B (baryon) | 6.10×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.04% |
| θ(H₂O) | 104.52° | 104.52° | 0.00° |
| δ_CKM | 68.75° | 68.8° | 0.1% |
| Ω_Λ | 0.6850 | 0.685 | 0.07% |
| sin²θ₁₃ | 0.0220 | 0.0220 | **-0.07σ** |
| sin²θ₁₂ | 0.3070 | 0.307 | **+0.002σ** |
| sin θ_C | 0.2263 | 0.2253 | **+0.86σ** |
| η/s (sQGP) | 1/(4π) | ~0.08 | exact |

## Repository Structure

```
book/               — THE BOOK: single source of truth for all theory
  main.tex          — Master file (6 Parts, 20 chapters, 2 appendices)
  chapters/         — ch01-ch20 + appendix_verification, appendix_code

papers/             — 3-tier publication strategy
  paper1_chiral_decomposition.tex    — Pure math (no physics language)
  paper2_frobenius_to_gauge.tex      — Math-physics bridge
  paper3_zero_parameter_predictions.tex — Full physics predictions

research-notes/     — Historical working documents (not authoritative)
lib/                — Core Python library (drlt.py, experiment.py)
experiments/        — Numerical experiments (EXP_001 ~ EXP_060)
results/            — Experiment outputs + EXPERIMENT_REPORT.md
```

## How to Run

```bash
cd experiments
python EXP_001_pipeline.py      # Pipeline verification (9/9)
python EXP_039_bond_angles.py   # CH₄/NH₃/H₂O bond angles
python EXP_041_hydrogen_exact.py # Hydrogen spectrum
python EXP_040_clean_scorecard.py # All fermion masses
```

## Book Structure

| Part | Chapters | Content |
|------|----------|---------|
| I. Foundation | 1-3 | Why ℂ, why d=5, (2,3) uniqueness |
| II. The Simplex | 4-5 | Combinatorial geometry, 3 variational theorems |
| III. Spacetime & Forces | 6-8 | Gram matrix → metric + gauge, ħ, couplings |
| IV. Matter | 9-11 | Fermion masses + Ξ correction, atoms/chemistry, mixing/CP |
| V. Completeness | 12-14 | Trace conservation, cosmology, block universe |
| VI. Applications | 15-20 | Yang-Mills, compact stars, Webb dipole, path integral, QCD, hydrogen precision |
| Appendices | A-B | Numerical verification, core algorithms |

See `CLAUDE.md` for detailed development guidelines and workflow rules.
