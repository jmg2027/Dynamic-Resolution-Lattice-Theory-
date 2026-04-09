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

## Code Structure
- `axiom/foundations.md` — Theory: axiom + 17 derivations
- `experiments/core.py` — Vertex + Network (true foundation)
- `experiments/simplex.py` — Simplex4D (legacy, compatible)
- `experiments/lattice.py` — Lattice with curvature
- All other experiment files import from these.

## Experiment Framework
- Every experiment script goes in `experiments/` with prefix `EXP_NNN_name.py`
- Each experiment MUST:
  1. Print a header with experiment number and title
  2. Save results to `results/EXP_NNN_name.txt` automatically
  3. Print a PASS/FAIL summary at the end
- Use `experiments/run_experiment.py` as the runner framework.
- Results are accumulated in `results/` and never deleted.

## Experiment Numbering
- EXP_001: Pipeline verification (ψ → W → g_μν → curvature)
- EXP_002: Black hole bounce (collapse → bounce → expansion)
- EXP_003: Time evolution (local Hamiltonians, spacetime restructuring)
- EXP_004: 1D force law profiles
- EXP_005: 4D lattice force law (1/r² convergence)
- EXP_006: Self-evolving universe (inflation → equilibrium)
- EXP_007: CMB power spectrum (n_s measurement)
- Next: EXP_008

## Git Rules
- Commit after each meaningful change with descriptive message.
- Always push to the designated branch.
- Never amend commits.
