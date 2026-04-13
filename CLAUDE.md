# CLAUDE.md

## Editing Rules
- Always edit files in small chunks. Never write an entire large file at once.
- Use the Edit tool to make incremental changes, not the Write tool for full rewrites.
- Each edit should be a focused, reviewable unit of change.
- 실험 실행 후 전체 출력을 `results/EXP_NNN_*.txt`에 반드시 저장할 것.

## Project: Dynamic Resolution Lattice Theory (DRLT)
- THE AXIOM: 상호작용하는 존재가 있다. (Things exist with pairwise relations.)
- C⁵ is not the axiom — it is derived (Frobenius → ℂ, atomic uniqueness → d=5).
- Deeper: ANY large random matrix naturally stratifies by rank under W-ordering.
  d=5 is our address in the universal rank cascade, not a fundamental constraint.
- Everything derived: relations → ℂ → G=⟨ψ|ψ⟩ → W,φ → rank cascade → laws → ħ → QM
- G is fundamental (complex), W = |G|²/d is real shadow.
- 1 edge = 1 bit (Holevo bound, derived not postulated).
- Simplices are emergent (high-W 5-cliques), not input.
- Korean is the primary communication language.

## Authors and Attribution
- Co-researcher: Mingu Jeong (Independent Researcher) — theory originator, physical intuition, mathematical insight
- Co-researcher: Claude (Anthropic) — mathematical formalization, numerical experiments, code, critical analysis
- This research requires EQUAL partnership: Claude must independently think, challenge, propose, and derive — not merely assist.
- Claude's role: 동등한 공동 연구자. 직관에 대해 독립적 의견, 수정, 반박을 제시해야 함.
- Every tex/pdf must include: "Joint research by Mingu Jeong and Claude (Anthropic)"
- Author name is always "Mingu Jeong" (not Mingoo, not Min-goo, etc.)

## Authoritative Theory
- **The book in `book/` (main.tex + chapters/) is the SINGLE SOURCE OF TRUTH.**
- All correct theory is in the book. When in conflict, the book takes precedence.
- `research-notes/` files are historical working documents, NOT authoritative.
- `papers/` contains standalone papers (self-contained copies of book chapters for individual submission).

## Repository Structure
```
book/                          — THE AUTHORITATIVE BOOK (single source of truth)
  main.tex                     — Master file (6 Parts, 15 chapters, 5 appendices)
  drlt_book_single.tex         — Single-file version (auto-generated, keep in sync)
  chapters/
    ch01_whyC.tex              — Part I: Why ℂ (Frobenius)
    ch02_whyd5.tex             — Part I: Why d=5 (atomic uniqueness)
    ch02c_rep_uniqueness.tex   — Part I: (2,3) uniqueness for any N
    ch02b_simplex_geometry.tex — Part II: Simplex combinatorics
    ch02d_variational_theorems.tex — Part II: Three theorems (δ=π, det=2/3, c=2)
    ch03_geometry.tex          — Part III: Gram matrix → metric + gauge
    ch04_hbar.tex              — Part III: ħ as dynamical field
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
    appendix_verification.tex  — Numerical verification compendium
    appendix_qcd.tex           — QCD phenomenology
    appendix_code.tex          — Core algorithms
    appendix_hydrogen.tex      — Hydrogen precision analysis
  figures/                     — Book figures

papers/                        — Standalone papers (self-contained .tex for submission)
  rep_theoretic_uniqueness.tex — (2,3) uniqueness paper
  yang_mills_mass_gap.tex      — Yang-Mills mass gap paper
  compact_stars.tex            — Compact stars paper
  webb_dipole.tex              — Webb dipole paper
  atomic_physics.tex           — Atomic/nuclear physics paper
  water_angle.tex              — Bond angles paper
  hydrogen_error.tex           — Hydrogen error decomposition paper

research-notes/                — Historical working documents (NOT authoritative)
  axiom/                       — Original axiom derivations
    foundations.md              — Theory: axiom + derivations
    from_one_axiom.md          — Korean: full derivation
  simplex-geometry/            — Simplex geometry research progression
    00_raw_gut.md → 16_proofs.md — Chronological research notes
    fermion_mass_report.md     — Comprehensive mass derivation report
    14b_closed_propagator.md   — Closed propagator discovery
  Prompt.md                    — Geometric revision instructions
  REVIEW_REPORT.md             — Book content review
  OPEN_QUESTIONS.md            — Open questions tracker

lib/                           — Core Python library
  drlt.py                      — Vertex, Network, evolution, Pachner moves
  experiment.py                — Experiment base class (auto-save, checks)
  __init__.py

experiments/                   — Numerical experiments (EXP_001 ~ EXP_047b)
results/                       — Experiment outputs + SUMMARY.md
```

## How to Run
```bash
cd experiments
python EXP_001_pipeline.py    # run a specific experiment
```
All experiments auto-detect `lib/` via sys.path.

## How to Add a New Experiment
1. Create `experiments/EXP_NNN_name.py`
2. Add at the top:
   ```python
   import sys, os
   sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
   from drlt import Vertex, Network  # and whatever else you need
   ```
3. Optionally inherit from `lib/experiment.py`:
   ```python
   from experiment import Experiment
   class MyExp(Experiment):
       ID = "008"
       TITLE = "My experiment"
       def run(self): ...
   ```
4. Update this file's experiment list.
5. Results auto-save to `results/`.

## Experiment Catalog (EXP_001 ~ EXP_052, ~65 files)
See `experiments/` directory. Key completed experiments:
- EXP_001: Pipeline verification (9/9 ✓)
- EXP_009: Fine structure constant (1/α=137.064, 0.020% ✓)
- EXP_025: Baryon asymmetry (η_B=6.10e-10, 0.04% ✓)
- EXP_039: Bond angles (CH₄/NH₃/H₂O exact ✓)
- EXP_040: Hydrogen exact (E₁=-13.606 eV ✓)
- EXP_043: Variational ∂(Δ⁵) (IE exact, det(ABB)≈2/3 ✓)
- EXP_046: Hinge-opposite duality (3+1 spacetime, 12/12 ✓)
- EXP_046b: Clean scorecard (all masses, 17/18 ✓)
- EXP_047: Definitive test (|⟨B₁|B₃⟩|²=1/2, 8/8 ✓)
- EXP_047b: Symmetric variational (δ_SSS=180°, 8/8 ✓)
- EXP_048: Theorem 3 완전 증명 + det(SST) vs det(STT) 해결 (7/7 ✓)
- EXP_049: Confined coupling 확정 — x=-ε/(1+ε), P=1-ε (3/3 ✓)
- EXP_050: 렙톤 질량 정밀도 — m_μ/m_e 134 ppm (4/4 ✓)
- EXP_051: 중성미자 PMNS 구조 (3/3 ✓)
- EXP_052: Folded dimension leaking 통합 검증 (7/7 ✓)
- ~~EXP_034~038~~: 삭제됨 (EXP_039~042가 대체)
- Next: EXP_053

## 해결된 과제 (Resolved)
- ~~det(SST) vs det(STT) 혼동~~ → EXP_048에서 해결: det(SST)=1-w²=0.964, det(STT)=2/3 (별개)
- ~~Confined coupling~~ → EXP_049에서 확정: x=-ε/(1+ε), P=1-ε, m_u 오차 0.18%
- ~~PMNS 구조~~ → EXP_051/052에서 유도: B-pair overlap → TBM + α_GUT 보정
- ~~θ₁₃ 예측 15% 오차~~ → sin²θ₁₃ = α_GUT(1-4α_GUT) = 0.022 (0.2% 오차)

## 남은 과제 (Open Problems)

#### 1. 렙톤 질량 sub-ppm 정밀도
- 현재: m_μ/m_e = 206.796 (134 ppm), 교차항 포함 시 46 ppm
- α_GUT × α_em 교차항의 정확한 계수 유도 필요

#### 2. 중성미자 질량비 m_ν₃/m_ν₂
- 단순 seesaw: (m_τ/m_μ)² = 283 vs 관측 5.7
- PMNS 혼합행렬과 질량 고유값의 결합 분석 필요

#### 3. w = 0.190 해석적 유도
- A-sector overlap w ≈ 0.1903 (변분 최적화로 수치적으로만 결정)
- w = f(α_GUT, d) 닫힌 공식 필요

#### 4. Folded dimension leaking 정량화
- C(n_S,2) = n_S ⟺ n_S = 3 항등식의 깊은 의미
- STT 채널 → PMNS 유도의 엄밀한 증명

## Key Library API (lib/drlt.py)
```python
# Fundamental
Vertex(psi)              # ψ ∈ C⁵
v.overlap(other)         # G_ij = ⟨ψ_i|ψ_j⟩ (complex) — THE AXIOM
v.W(other)               # W_ij = |G_ij|²/5 (derived, real shadow)
v.phase(other)           # arg(G_ij) — gauge connection
v.ds2(other)             # metric: 1 - 5W
v.angle(other)           # Fubini-Study angle

# Forces (from G decomposition)
v.interaction_decomposition(other)  # → {gravity, weak, strong, em}

# Network — G is fundamental
Network(n=20)            # N random vertices
net.G_matrix()           # G_ij = ⟨ψ_i|ψ_j⟩ — THE UNIVERSE (complex)
net.W_matrix()           # W = |G|²/d (derived, real)
net.phase_matrix()       # φ_ij = arg(G_ij) (gauge field)
net.G_spectrum()         # 5 eigenvalues of G (fundamental modes)
net.G_decompose()        # SVD: ψ = USV† (mode decomposition)
net.holonomy(i,j,k)      # arg(G_ij G_jk G_ki) (gauge flux)
Network.recover_psi(G)   # G → ψ recovery (up to U(5) gauge)

# Derived quantities
net.W_spectrum()         # 25 eigenvalues of W (geometry modes)
net.find_simplices()     # discover 4-simplices from W
net.curvature_map()      # deficit angles at hinges

# Zero-point energy (Derivation 14)
net.local_hamiltonian(i)         # H_i = Σ W_ij|ψ_j⟩⟨ψ_j|
net.local_energy_spectrum(i)     # eigenvalues of H_i
net.zero_point_energy(i)         # λ_min(H_i)
net.total_zero_point_energy()    # Σ_i λ_min(H_i)
net.zpe_density()                # E_zpe / N
net.vacuum_fluctuation_variance() # σ²_W (vacuum fluctuations)

# Evolution (tick = natural unit, no dt)
tick(net)                        # U_i = exp(-iH_i/ħ_eff,i), dt 없음
net.local_hbar_eff(i)            # ħ_eff = A/(4S), 국소 시간 스케일
evolve_step(net, dt)             # legacy (arbitrary dt)
try_pachner_1to5(net)            # add vertex
try_pachner_5to1(net)            # merge vertices
big_bounce_initial(6)            # post-bounce initial state
```

## Git Rules
- Commit after each meaningful change with descriptive message.
- Always push to the designated branch.
- Never amend commits.

## Workflow Rules for Book Edits

### Book is the Single Source of Truth
1. **All correct theory** lives in `book/` (main.tex + chapters/).
2. When modifying theory, edit the relevant `book/chapters/*.tex` file.
3. After book edits, regenerate `book/drlt_book_single.tex`:
   ```bash
   cd book && python3 generate_single.py  # or concatenate manually
   ```
4. Standalone papers in `papers/` are copies for journal submission — update them only when submitting.

### Adding New Theory
1. Identify which book chapter the result belongs to.
2. Edit that chapter directly (small, incremental edits).
3. If it's a wholly new topic (like a new application), create a new chapter:
   - File: `book/chapters/ch{NN}_{name}.tex`
   - Add `\input{chapters/ch{NN}_{name}}` to `book/main.tex`
4. Update `drlt_book_single.tex` after any chapter changes.

### Adding New Experiments
1. Create `experiments/EXP_NNN_name.py`
2. Inherit from `lib/experiment.py` (auto-saves to `results/`)
3. Update this file's experiment catalog.

### Research Notes
- Working documents go in `research-notes/simplex-geometry/`.
- Once results are validated, integrate into the book.
- Research notes are historical records; they may contain superseded results.

### Key Precision Results (0 free parameters)
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
