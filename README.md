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
  → 3 variational theorems: δ_SSS=π, ⟨det(STT)⟩=2/3, c=2
  → Closed propagator: P(x) = (1+2x)/(1+x) — exact Dyson resummation
  → 52+ physical observables, ZERO free parameters
```

## Key Results (0 free parameters)

| Quantity | DRLT | Observed | Error |
|----------|------|----------|-------|
| 1/α_em | 137.064 | 137.036 | 0.020% |
| m_p (proton) | 938.27 MeV | 938.27 MeV | **0.000%** |
| m_μ/m_e | 206.80 | 206.768 | 0.02% |
| m_τ/m_μ | 16.816 | 16.817 | 0.006% |
| m_H (Higgs) | 125 GeV | 125.25 GeV | 0.2% |
| η_B (baryon) | 6.10×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.04% |
| θ(H₂O) | 104.52° | 104.52° | 0.00° |
| δ_CKM | 68.75° | 68.8° | 0.1% |
| Ω_Λ | 0.6850 | 0.685 | 0.07% |
| η/s (sQGP) | 1/(4π) | ~0.08 | exact |

Median accuracy across all fermion masses: **0.07%**.

## Repository Structure

```
book/               — THE BOOK: single source of truth for all theory
  main.tex          — Master file (6 Parts, 15 chapters, 5 appendices)
  drlt_book_single.tex — Single-file version (auto-generated)
  chapters/         — All chapter .tex files

papers/             — Standalone papers for journal submission
research-notes/     — Historical working documents (not authoritative)
lib/                — Core Python library (drlt.py, experiment.py)
experiments/        — Numerical experiments (EXP_001 ~ EXP_047b)
results/            — Auto-saved experiment outputs
```

## How to Run

```bash
cd experiments
python EXP_001_pipeline.py      # Pipeline verification (9/9)
python EXP_039_bond_angles.py   # CH₄/NH₃/H₂O bond angles
python EXP_040_hydrogen_exact.py # Hydrogen spectrum from one formula
python EXP_046b_clean_scorecard.py # All fermion masses
```

## Book Structure

| Part | Chapters | Content |
|------|----------|---------|
| I. Foundation | 1-3 | Why ℂ, why d=5, (2,3) uniqueness |
| II. The Simplex | 4-5 | Combinatorial geometry, 3 variational theorems |
| III. Spacetime & Forces | 6-8 | Gram matrix → metric + gauge, ħ, couplings |
| IV. Matter | 9-11 | Fermion masses, atoms/chemistry, mixing/CP |
| V. Completeness | 12-14 | Trace conservation, cosmology, block universe |
| VI. Applications | 15-17 | Yang-Mills mass gap, compact stars, Webb dipole |
| Appendices | A-E | Path integral, verification, QCD, algorithms, hydrogen |

See `CLAUDE.md` for detailed development guidelines and workflow rules.
