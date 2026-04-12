# CLAUDE.md

## Editing Rules
- Always edit files in small chunks. Never write an entire large file at once.
- Use the Edit tool to make incremental changes, not the Write tool for full rewrites.
- Each edit should be a focused, reviewable unit of change.
- 실험 실행 후 전체 출력을 `results/EXP_NNN_*.txt`에 반드시 저장할 것. Experiment 클래스가 자동 저장하지만, 스크립트 직접 실행 시에도 출력을 파일로 리다이렉트하거나 tee로 저장.

## Project: Dynamic Resolution Lattice Theory (DRLT)
- THE AXIOM: 상호작용하는 존재가 있다. (Things exist with pairwise relations.)
- C⁵ is not the axiom — it is derived (Frobenius → C, atomic uniqueness → d=5).
- Deeper: ANY large random matrix naturally stratifies by rank under W-ordering.
  d=5 is our address in the universal rank cascade, not a fundamental constraint.
- Everything derived: relations → C → G=⟨ψ|ψ⟩ → W,φ → rank cascade → laws → ħ → QM
- G is fundamental (complex), W = |G|²/d is real shadow.
- 1 edge = 1 bit (Holevo bound, derived not postulated).
- Simplices are emergent (high-W 5-cliques), not input.
- Korean is the primary communication language.

## Author and Attribution
- Author: Mingu Jeong (Independent Researcher)
- AI assistant: Claude (Anthropic) — code, numerical experiments, LaTeX, editorial
- All theoretical content, physical insights, and mathematical derivations are by the author
- Every tex/pdf must include AI disclosure: "Developed with assistance from Claude (Anthropic)"
- Author name is always "Mingu Jeong" (not Mingoo, not Min-goo, etc.)

## Authoritative Theory
- The book in `book/` (main.tex + chapters/) is the authoritative, correct formulation.
- `axiom/` files are historical drafts — some use older W-based axiom or d=4 as input.
- When in conflict, the book takes precedence over everything else in the repo.

## Repository Structure
```
lib/
  drlt.py          — Core library: Vertex, Network, evolution, Pachner moves
  experiment.py    — Experiment base class (auto-save, checks)
  __init__.py

experiments/
  EXP_001_pipeline.py   — Pipeline verification (9/9 ✓)
  EXP_002_bounce.py     — Black hole bounce
  EXP_003_evolution.py  — Time evolution
  EXP_004_force_1d.py   — 1D force profiles
  EXP_005_force_4d.py   — 4D lattice 1/r²
  EXP_006_universe.py   — Self-evolving universe
  EXP_007_cmb.py        — CMB power spectrum

axiom/
  foundations.md   — Theory: axiom + 17 derivations

results/
  SUMMARY.md       — All experiment results
  EXP_NNN_*.txt    — Auto-saved outputs
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

## Experiment Catalog
- EXP_001: Pipeline verification (ψ → W → g_μν → curvature)
- EXP_002: Black hole bounce (collapse → bounce → expansion)
- EXP_003: Time evolution (local Hamiltonians, spacetime restructuring)
- EXP_004: 1D force law profiles
- EXP_005: 4D lattice force law (1/r² convergence)
- EXP_006: Self-evolving universe (inflation → equilibrium)
- EXP_007: CMB power spectrum (n_s measurement)
- EXP_008: Zero-point energy (영점 에너지 유도 및 측정, 7/7 ✓)
- EXP_009: Fine structure constant (미세구조상수, 6/6 ✓)
- EXP_010: Galaxy rotation curves (은하 회전 곡선 & 암흑물질, 4/4 ✓)
- EXP_011: Black hole simulation (블랙홀 생애 시뮬레이션, 5/7)
- EXP_012: Gravitational waves (중력파 검출, 4/4 ✓)
- EXP_013: Entanglement & Bell (얽힘/벨 부등식, 1/4 — 얽힘 구조 탐색 중)
- EXP_014: Particles from geometry (입자=기하학, 5/5 ✓)
- EXP_015: All physics from C⁵ (전체 물리 법칙 카탈로그, 25/25 ✓)
- EXP_016: Neutrino mass (중성미자 질량 & 시소 메커니즘, 3/4)
- EXP_017: Yukawa running (유카와 β 함수 격자 유도, 3/3 ✓)
- EXP_018: Precision constants (정밀 상수 종합: 세 공식+β+쿼크질량+카르탄+3줄증명, 5/5 ✓)
- EXP_019: C² mixing (C² 혼합 행렬 → CKM/PMNS 구조, 4/4 ✓)
- EXP_020: Block universe (블록 우주 정적 대각화, 5/5 ✓)
- EXP_021: Pachner block (블록 우주에서 Pachner = 유효 N = 줌인, 5/5 ✓)
- EXP_022: Cosmic history (W 고유값 스펙트럼 = 우주 역사, 5/5 ✓)
- EXP_023: Cosmic mysteries (우주론 미스테리 8개 재해석, 8/8 ✓)
- EXP_024: Large-N cosmos (N=10000 스케일링, 허블텐션, 구조형성, 5/5 ✓)
- EXP_025: Baryon asymmetry (η_B = 0.68/√C(5⁹,3) = 6.10e-10, 관측 일치!, 5/5 ✓)
- EXP_026: CMB spectrum (W 고유모드 파워 스펙트럼, 피크 7개, n_s<1, 5/5 ✓)
- EXP_027: Rank 25 (rank(W)=5²=25 정리 증명, 우주=200 bytes, 진행중)
- EXP_028: 200 bytes (25개 고유값=물리 전체? SU(5)분해+M_H+Λ+τ_p, 5/5 ✓)
- EXP_029: QCD/sQGP (CP⁴→Δ⁴ 모멘트맵, W/φ분해, C³ 구속/해방/sQGP/점근적자유, 9/9 ✓)
- EXP_030: Constraint propagation (rank(G)≤5 → 블록우주, tick() 수렴, 25 자유도=SU(5), 7/7 ✓)
- EXP_031: Simplex spacetime (심플렉스 격자 시공간 모델, 4/5)
- EXP_032: Compact stars (중성자별/쿼크별 det(G_h) 계층, 6/6 ✓)
- EXP_033: Webb dipole (ghost 공간변동 정합성, α_s↔α_em 역상관, 7/7 ✓)
- EXP_033b: Webb vs μ (μ ghost-protected 발견, 자기교정, 1/3)
- EXP_039: Bond angles (CH₄/NH₃/H₂O from n_S=3, 전부 exact, 4/4 ✓)
- EXP_040: Hydrogen exact (E_n = -m_e α²/(n_T n²), 1/2=1/n_T, 4/4 ✓)
- EXP_041: Rank cascade (랜덤 행렬 rank 층위 관찰, 2/2 ✓)
- EXP_042: Regge atoms (정확한 Regge action으로 원자 계산, Phase 1a ✓, 진행중)
- ~~EXP_034~038~~: 삭제됨 (ad hoc 에너지 함수, EXP_039~042가 대체)
- Next: EXP_043

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
