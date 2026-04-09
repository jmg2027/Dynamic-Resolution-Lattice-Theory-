# CLAUDE.md

## Editing Rules
- Always edit files in small chunks. Never write an entire large file at once.
- Use the Edit tool to make incremental changes, not the Write tool for full rewrites.
- Each edit should be a focused, reviewable unit of change.

## Project: Dynamic Resolution Lattice Theory (DRLT)
- Refined Axiom: N vertices with ψ ∈ C⁵, W_ij = |⟨ψ_i|ψ_j⟩|²/5. That's it.
- Simplices are emergent (high-W 5-cliques), not input.
- All physics is derived, not postulated.
- Korean is the primary communication language.

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
- Next: EXP_015

## Key Library API (lib/drlt.py)
```python
# Fundamental
Vertex(psi)              # ψ ∈ C⁵
v.W(other)               # THE AXIOM: |⟨ψ_i|ψ_j⟩|²/5
v.ds2(other)             # metric: 1 - 5W
v.angle(other)           # Fubini-Study angle
v.overlap(other)         # ⟨ψ_i|ψ_j⟩ (complex)

# Forces
v.interaction_decomposition(other)  # → {gravity, weak, strong, em}

# Network
Network(n=20)            # N random vertices
net.W_matrix()           # full W_ij
net.find_simplices()     # discover 4-simplices from W
net.curvature_map()      # deficit angles at hinges

# Zero-point energy (Derivation 14)
net.local_hamiltonian(i)         # H_i = Σ W_ij|ψ_j⟩⟨ψ_j|
net.local_energy_spectrum(i)     # eigenvalues of H_i
net.zero_point_energy(i)         # λ_min(H_i)
net.total_zero_point_energy()    # Σ_i λ_min(H_i)
net.zpe_density()                # E_zpe / N
net.W_spectrum()                 # eigenvalues of W matrix
net.vacuum_fluctuation_variance() # σ²_W (vacuum fluctuations)

# Evolution
evolve_step(net, dt)     # self-consistent local H
try_pachner_1to5(net)    # add vertex
try_pachner_5to1(net)    # merge vertices
big_bounce_initial(6)    # post-bounce initial state
```

## Git Rules
- Commit after each meaningful change with descriptive message.
- Always push to the designated branch.
- Never amend commits.
