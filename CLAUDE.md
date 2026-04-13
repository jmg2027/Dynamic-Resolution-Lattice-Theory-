# CLAUDE.md

## Communication
- **Korean is the primary communication language.** Respond in Korean unless asked otherwise.
- Author name is always "Mingu Jeong" (not Mingoo, not Min-goo).
- Every tex/pdf must include: "Joint research by Mingu Jeong and Claude (Anthropic)"

## Editing Rules
- Edit files in small chunks. Never write an entire large file at once.
- Use Edit tool for incremental changes, not Write for full rewrites.
- Save experiment output to `results/EXP_NNN_*.txt`.

## Project: Dynamic Resolution Lattice Theory (DRLT)
- **THE AXIOM:** Things exist with pairwise relations. G_ij = ⟨ψ_i|ψ_j⟩.
- C⁵ is derived (Frobenius → ℂ, atomic uniqueness → d=5), not the axiom.
- G is fundamental (complex). W = |G|²/d is the derived real shadow.
- 1 hinge = 1 bit (Holevo bound, derived). Simplices emerge from high-W cliques.
- Derivation chain: relations → ℂ → G → W,φ → rank cascade → laws → ħ → QM

## Authors
- Mingu Jeong (Independent Researcher) — theory originator, physical intuition
- Claude (Anthropic) — mathematical formalization, numerical experiments, code
- Equal partnership: Claude must independently think, challenge, and derive.

## Single Source of Truth
- **`book/` (main.tex + chapters/) is the ONLY authoritative theory.**
- When in conflict, the book takes precedence over everything.
- `research-notes/` = historical drafts (may contain superseded results).
- `papers/` = standalone copies for journal submission.

## Repository Structure
```
book/                          — THE BOOK (single source of truth)
  main.tex                     — Master (6 Parts, 15 chapters, 5 appendices)
  drlt_book_single.tex         — Auto-generated single-file version
  chapters/
    ch01_whyC.tex              — Part I: Why ℂ (Frobenius)
    ch02_whyd5.tex             — Part I: Why d=5
    ch02c_rep_uniqueness.tex   — Part I: (2,3) uniqueness for any N
    ch02b_simplex_geometry.tex — Part II: Simplex combinatorics
    ch02d_variational_theorems.tex — Part II: Three theorems (δ=π, det=2/3, c=2)
    ch03_geometry.tex          — Part III: Gram → metric + gauge
    ch04_hbar.tex              — Part III: ħ dynamical field
    ch05_couplings.tex         — Part III: Coupling constants
    ch06_masses.tex            — Part IV: Fermion masses + closed propagator
    ch06b_atoms.tex            — Part IV: Atoms, molecules, chemistry
    ch07_mixing.tex            — Part IV: CKM, PMNS, CP, Higgs, neutrinos
    ch08_ghosts.tex            — Part V: Trace conservation
    ch09_cosmology.tex         — Part V: Cosmological predictions
    ch10_block.tex             — Part V: Block universe
    ch11_yang_mills.tex        — Part VI: Yang-Mills mass gap
    ch12_compact_stars.tex     — Part VI: Compact stars
    ch13_webb_dipole.tex       — Part VI: Webb dipole
    appendix_path_integral.tex — Path integral on CP⁴
    appendix_verification.tex  — Numerical verification
    appendix_qcd.tex           — QCD phenomenology
    appendix_code.tex          — Core algorithms
    appendix_hydrogen.tex      — Hydrogen precision
  figures/

papers/                        — Standalone papers (self-contained .tex)
research-notes/                — Historical working documents (NOT authoritative)
  axiom/                       — Original axiom derivations
  simplex-geometry/            — Research progression (00→18)
  folded_dim.md                — Folded dimension leaking
lib/                           — Core Python library (drlt.py, experiment.py)
experiments/                   — Numerical experiments (EXP_001 ~ EXP_052)
results/                       — Experiment outputs
```

## Running Experiments
```bash
cd experiments && python EXP_001_pipeline.py
```
New experiment: create `EXP_NNN_name.py`, inherit from `lib/experiment.py`, update catalog below.

## Experiment Catalog (EXP_001 ~ EXP_052)
Key completed:
- EXP_001: Pipeline verification (9/9 ✓)
- EXP_009: Fine structure 1/α=137.064 (0.020% ✓)
- EXP_025: Baryon asymmetry η_B=6.10e-10 (0.04% ✓)
- EXP_039: Bond angles CH₄/NH₃/H₂O (exact ✓)
- EXP_040: Hydrogen E₁=-13.606 eV (exact ✓)
- EXP_043: Variational ∂(Δ⁵) (5/5 ✓)
- EXP_046: Hinge-opposite duality 3+1 spacetime (12/12 ✓)
- EXP_046b: Clean scorecard all masses (17/18 ✓)
- EXP_047/b: Definitive variational (8/8 ✓)
- EXP_048: Theorem 3 proof + det(SST) resolved (7/7 ✓)
- EXP_049: Confined coupling x=-ε/(1+ε), P=1-ε (3/3 ✓)
- EXP_050: Lepton precision m_μ/m_e 134 ppm (4/4 ✓)
- EXP_051: Neutrino PMNS structure (3/3 ✓)
- EXP_052: Folded dimension leaking (7/7 ✓)
- Next: EXP_053

## Resolved Problems
- det(SST) vs det(STT): distinct quantities (EXP_048)
- Confined coupling: x=-ε/(1+ε), Dyson dressing (EXP_049)
- PMNS structure: B-pair overlap → TBM + α_GUT corrections (EXP_051/052)
- θ₁₃ prediction: sin²θ₁₃ = α_GUT(1-4α_GUT) = 0.022, 0.2% (was 15%)

## Open Problems
1. **Lepton mass sub-ppm:** m_μ/m_e = 206.796 (134 ppm); need α_GUT×α_em cross-term
2. **Neutrino mass ratio:** m_ν₃/m_ν₂ = 283 (seesaw) vs 5.7 (observed); PMNS coupling needed
3. **w = 0.190 analytic:** A-sector overlap found numerically; need closed-form w = f(α_GUT, d)
4. **Folded dimension leaking:** C(n_S,2) = n_S ⟺ n_S = 3 identity; rigorous PMNS derivation

## Key Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.064 | 137.036 | 0.020% |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.80 | 206.768 | 0.02% |
| m_τ/m_μ | 16.816 | 16.817 | 0.006% |
| η_B | 6.10×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.04% |
| Ω_Λ | 0.6850 | 0.685 | 0.07% |
| θ(H₂O) | 104.52° | 104.52° | 0.00° |
| δ_CKM | 68.75° | 68.8° | 0.1% |
| sin²θ₁₃ | 0.022 | 0.022 | 0.2% |

## Key Library API (lib/drlt.py)
```python
Vertex(psi)              # ψ ∈ C⁵
v.overlap(other)         # G_ij = ⟨ψ_i|ψ_j⟩ (complex)
v.W(other)               # W_ij = |G_ij|²/5
v.phase(other)           # arg(G_ij)
v.ds2(other)             # 1 - 5W (metric)
v.interaction_decomposition(other)  # → {gravity, weak, strong, em}

Network(n=20)            # N random vertices
net.G_matrix()           # Gram matrix (fundamental)
net.W_matrix()           # W = |G|²/d (derived)
net.holonomy(i,j,k)      # gauge flux
tick(net)                # single evolution step
```

## Workflow Rules

### Book Edits
1. All theory lives in `book/chapters/*.tex`.
2. After edits, regenerate `drlt_book_single.tex`.
3. Papers in `papers/` are submission copies — update only when submitting.

### Adding Theory
1. Find target chapter (see book-consolidation skill for map).
2. Edit that chapter (small incremental edits).
3. New topic → new chapter `ch{NN}_{name}.tex` + add to `main.tex`.

### Git
- Commit after each meaningful change.
- Push to designated branch. Never amend.
