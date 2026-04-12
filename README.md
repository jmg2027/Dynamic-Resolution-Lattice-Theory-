# Dynamic Resolution Lattice Theory (DRLT)

**Author:** Mingoo Jeong (Independent Researcher)
**AI Assistant:** Claude (Anthropic) — code, numerical experiments, LaTeX, editorial

A theory deriving all of physics from a single axiom: *things exist with pairwise relations*.

## The Axiom

Points exist. Between every pair, there is a relation G_ij ∈ ℂ. That is all.

From this: ℂ is the unique substrate (Frobenius), (2,3) is the unique chiral structure (for any N), SU(3)×SU(2)×U(1) is the unique gauge group, α_GUT = 6/(25π²) is a theorem of mathematics, and all 52+ physical observables follow with zero free parameters.

## Structure

```
book/           — The authoritative book (main.tex + 15 chapters + 4 appendices)
                  + 6 standalone papers (.tex/.pdf)
lib/            — Core library (drlt.py, experiment.py)
experiments/    — 38 numerical experiments (EXP_001 through EXP_042)
results/        — Auto-saved outputs + solutions
axiom/          — Historical derivation documents (reference only)
```

## Key Results

| Quantity | DRLT | Observed | Error |
|----------|------|----------|-------|
| 1/α_em | 137.064 | 137.036 | 0.02% |
| m_p | 937.5 MeV | 938.3 MeV | 0.08% |
| η_B | 6.13×10⁻¹⁰ | 6.12×10⁻¹⁰ | 0.2% |
| θ(H₂O) | 104.52° | 104.52° | 0.00° |
| η/s (sQGP) | 1/(4π) | ~0.08 | exact |
| Ω_Λ | 0.682 | 0.685 | 0.5% |

Free parameters: **0**.

## How to Run

```bash
cd experiments
python EXP_001_pipeline.py    # basic verification
python EXP_039_bond_angles.py # water angle in one division
python EXP_040_hydrogen_exact.py # hydrogen spectrum
```

See `CLAUDE.md` for the full experiment catalog and development guidelines.
