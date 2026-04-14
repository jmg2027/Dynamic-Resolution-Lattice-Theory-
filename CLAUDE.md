# CLAUDE.md

## Session Start
- **If HANDOFF.md exists, read it FIRST** before doing anything else.
- It contains the previous session's context, open problems, and next steps.
- After reading, summarize key points and ask what to work on.

## Communication
- **Korean is the primary communication language.** Respond in Korean unless asked otherwise.
- Author name is always "Mingu Jeong" (not Mingoo, not Min-goo).
- Every tex/pdf must include: "Joint research by Mingu Jeong and Claude (Anthropic)"

## Editing Rules (1원칙: 청크)
- **새 파일 작성 시 100줄 이하 청크로 나눠 Write → Edit 반복.** 절대 한번에 200줄 이상 쓰지 않는다.
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
  main.tex                     — Master (6 Parts, 20 chapters, 2 appendices)
  drlt_book_single.tex         — Auto-generated single-file version
  chapters/
    ch01_whyC.tex              — Part I: Why ℂ (Frobenius)
    ch02_whyd5.tex             — Part I: Why d=5
    ch03_rep_uniqueness.tex    — Part I: (2,3) uniqueness for any N
    ch04_simplex_geometry.tex  — Part II: Simplex combinatorics
    ch05_variational_theorems.tex — Part II: Three theorems (δ=π, det=2/3, c=2)
    ch06_geometry.tex          — Part III: Gram → metric + gauge
    ch07_hbar.tex              — Part III: ħ dynamical field
    ch08_couplings.tex         — Part III: Coupling constants
    ch09_masses.tex            — Part IV: Fermion masses + Ξ correction
    ch10_atoms.tex             — Part IV: Atoms, molecules, chemistry
    ch11_mixing.tex            — Part IV: CKM, PMNS, CP, neutrinos, w=3/(5π)
    ch12_ghosts.tex            — Part V: Trace conservation
    ch13_cosmology.tex         — Part V: Cosmological predictions
    ch14_block.tex             — Part V: Block universe
    ch15_yang_mills.tex        — Part VI: Yang-Mills mass gap
    ch16_compact_stars.tex     — Part VI: Compact stars
    ch17_webb_dipole.tex       — Part VI: Webb dipole
    ch18_path_integral.tex     — Part VI: Path integral + YM/EH emergence
    ch19_qcd.tex               — Part VI: QCD phenomenology, KSS bound
    ch20_hydrogen.tex          — Part VI: Hydrogen precision, 4-level decomposition
    appendix_verification.tex  — Numerical verification compendium
    appendix_code.tex          — Core algorithms
  figures/

papers/                        — Standalone papers (self-contained .tex)
research-notes/                — Historical working documents (NOT authoritative)
  axiom/                       — Original axiom derivations
  simplex-geometry/            — Research progression (00→18)
  folded_dim.md                — Folded dimension leaking
lib/                           — Core Python library (drlt.py, experiment.py)
experiments/                   — Numerical experiments (EXP_001 ~ EXP_044)
results/                       — Experiment outputs
```

## Running Experiments
```bash
cd experiments && python EXP_001_pipeline.py
```
New experiment: create `EXP_NNN_name.py`, inherit from `lib/experiment.py`, update catalog below.

## Experiment Catalog (EXP_001 ~ EXP_070)
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
- EXP_053: Lepton mass 26 ppm → sub-ppb via 3-step Ξ chain (3/3 ✓)
- EXP_053b: Convergent series + closed form (99.99997% ✓)
- EXP_054: Neutrino ratio democratic seesaw 283→3.73 (3/3 ✓)
- EXP_055: w = 3/(5π) analytic closed form (3/3 ✓)
- EXP_056: Rigorous PMNS C(n,2)=n uniqueness (4/4 ✓)
- EXP_057: m_τ/m_μ hop series 55→5 ppm (3/3 ✓)
- EXP_058: PMNS precision all 4 angles <2σ (5/5 ✓)
- EXP_059: CKM precision sin θ_C +0.86σ (4/5 ✓, Higgs marginal)
- EXP_060: Absolute masses Ξ correction 8/12 improved (8/12 ✓)
- EXP_061: n-p mass diff geometric factor issue (diagnostic)
- EXP_062: Remaining observables 1/α_em 0.0004% (5/5 ✓)
- EXP_067: Zeta spectral dim, sector weight, β matching (9/9 ✓)
- EXP_069: δS/δψ=0 on ∂(Δ⁵) — flat vacuum + δ(AAA)=π (6/6 ✓)
- EXP_070: Helium IE = 2Ry(1-c²α_GUT) = 24.565 eV, 0.089% (5/5 ✓)
- EXP_071: Higgs quartic λ = (1+α_GUT)²/(2c²), m_H=125.9 GeV +0.51% (10/10 ✓)
- Next: EXP_072

## Resolved Problems
- det(SST) vs det(STT): distinct quantities (EXP_048)
- Confined coupling: x=-ε/(1+ε), Dyson dressing (EXP_049)
- PMNS structure: B-pair overlap → TBM + α_GUT corrections (EXP_051/052)
- θ₁₃ prediction: sin²θ₁₃ = α_GUT(1-4α_GUT) = 0.022, 0.2% (was 15%)
- **Lepton mass sub-ppb:** Ξ = α_em/(1-α)+α/(d²-1)+α_em² → 0.7 ppb (EXP_053/053b)
- **Neutrino ratio:** Democratic seesaw D×T⁻¹×D → 283→3.73 (EXP_054)
- **w closed form:** w = 3/(5π) = n_S/(d·π) (EXP_055)
- **PMNS rigorous:** C(n,2)=n ⟺ n=3; all 4 angles <2σ (EXP_056/058)
- **CKM precision:** sin θ_C +2.47σ → +0.86σ via Ξ chain (EXP_059)
- **1/α_em precision:** 0.020% → 0.0004% via same Ξ (EXP_062)
- **Higgs quartic:** λ=(1+α_GUT)²/(2c²) from face-level BC; 3.2%→0.51% (EXP_071)

## Open Problems
1. **Higgs mass residual:** m_H = 125.9 vs 125.25 GeV (0.51%); higher-order correction?
2. **Δm_np geometric factor:** +11% overcount; need correct combinatorial form
3. **1/α₂ (weak):** 18.2 vs 29.6; RGE running not yet included
4. **Neutrino ratio quantitative:** 3.73 vs 5.71 (35% gap); higher-order T-matrix needed
5. **1st gen quark masses:** Ξ correction degrades m_u, m_d; need confined-specific Ξ

## Key Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.7 ppb** |
| m_τ/m_μ | 16.8169 | 16.8170 | **5 ppm** |
| η_B | 6.10×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.04% |
| Ω_Λ | 0.6850 | 0.685 | 0.07% |
| θ(H₂O) | 104.52° | 104.52° | 0.00° |
| δ_CKM | 68.75° | 68.8° | 0.1% |
| sin²θ₁₃ | 0.0220 | 0.0220 | **-0.07σ** |
| sin²θ₁₂ | 0.3070 | 0.307 | **+0.002σ** |
| sin θ_C | 0.2263 | 0.2253 | **+0.86σ** |
| b₂ (1-loop β) | -3.163 | -3.167 | **0.11%** |
| IE(He) | 24.565 eV | 24.587 eV | 0.089% |
| m_H | 125.9 GeV | 125.25 GeV | **+0.51%** |
| λ (quartic) | 0.1312 | 0.1294 | +1.4% |

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
