# Dynamic Resolution Lattice Theory (DRLT)

**Author:** Mingu Jeong (Independent Researcher)  
**AI Assistant:** Claude (Anthropic) — code, numerical experiments, LaTeX, editorial

## The Axiom

Points exist. Between every pair, there is a relation G_ij = ⟨ψ_i|ψ_j⟩ ∈ ℂ. That is all.

## Derivation Chain

```
Points with relations
  → ℂ is the unique substrate (Frobenius theorem)
  → d = 5 is the unique dimension (atomic uniqueness + swap annihilation)
  → (2,3) is the unique chiral structure (representation-theoretic, for any N)
  → SU(3)×SU(2)×U(1) is the unique gauge group
  → α_GUT = 6/(25π²) is a theorem of mathematics
  → 52+ physical observables, zero free parameters
```

G_ij is fundamental (complex, Hermitian, rank ≤ 5). W_ij = |G_ij|²/d is the derived real shadow. Spacetime is a network of 4-simplices; each hinge (triangle) carries 1 bit. Forces are hinge types (SSS = strong, SST = EM, STT = weak). Gravity is the deficit angle between hinges.

## Key Results

| Quantity | DRLT | Observed | Error |
|----------|------|----------|-------|
| 1/α_em | 137.064 | 137.036 | 0.02% |
| m_p | 937.5 MeV | 938.3 MeV | 0.08% |
| m_H | 125 GeV | 125.25 GeV | 0.2% |
| η_B | 6.13×10⁻¹⁰ | 6.12×10⁻¹⁰ | 0.2% |
| θ(H₂O) | 104.52° | 104.52° | 0.00° |
| η/s (sQGP) | 1/(4π) | ~0.08 | exact |
| Ω_Λ | 0.682 | 0.685 | 0.5% |

Free parameters: **0**. Observational inputs: **0**.

## Structure

```
book/           — The authoritative book (main.tex + 10 chapters + 4 appendices)
                  + 6 standalone papers (.tex/.pdf)
lib/            — Core library (drlt.py 866 lines, experiment.py)
experiments/    — Numerical experiments (EXP_001 through EXP_042)
results/        — Auto-saved outputs + solution data (.npz)
axiom/          — Historical derivation documents (reference only)
```

## How to Run

```bash
cd experiments
python EXP_001_pipeline.py      # pipeline verification (9/9)
python EXP_039_bond_angles.py   # CH₄/NH₃/H₂O bond angles
python EXP_040_hydrogen_exact.py # hydrogen spectrum from one formula
```

See `CLAUDE.md` for the full experiment catalog and development guidelines.
