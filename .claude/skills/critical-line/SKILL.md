---
name: critical-line
description: "Explore and develop the DRLT → critical line connection (RH, GRH, L-functions, Yang-Mills). Triggered by: 'RH', 'Riemann', '리만', 'zeta', '제타', 'critical line', '임계선', 'Möbius', '뫼비우스', 'phase uniformity', '위상 균일', 'CLT boundary', 'GRH', 'L-function', 'Yang-Mills', 'Lean', 'PMF'."
---

# Critical Line Skill

Manage the unified critical-line sub-project (formerly rh-connection + gram-algebra).

**Working directory:** `critical-line/`

## The Complete Chain (memorize this)

**The number 2 is the unique doubly irreducible number:**
- Additive atoms = {2, 3}, Extension atoms over ℝ = {2}
- Intersection = {2} → dim_ℝ(ℂ) = n_T = 2

**Branch A: Why Re(s) = 1/2 (UNIVERSAL)**
```
|coefficient| = 1 → CLT: Var = Σ 1/k^{2σ} → σ_stat = 1/2
  (The "2" in |·|² = L² norm exponent = dim_ℝ(ℂ))
```

**Branch B: Why GUE statistics (ℂ-SPECIFIC)**
```
ℂ unique → β=2 → GUE → pair correlation matches ζ zeros
```

**Branch C: Functional equation (σ_func = 1/2)**
```
θ(x) = Σ e^{-πn²x} → Mellin → ζ(2s) → s/2
  (The "2" in n² = L² norm = dim_ℝ(ℂ))
```

**Unification (Two Boundaries + Doubly Irreducible):**
```
1/2 = 1/n_T = 1/dim_ℝ(ℂ) = 1/c = σ_stat = σ_geom = σ_func
All from the unique doubly irreducible number 2.
```

**Common foundation:**
```
ℂ unique → ℂ⁵ = ℂ² ⊕ ℂ³ → d²=25 channels → s=2 → ζ(2) = π²/6
```

## Directory Structure

```
critical-line/
├── CLAUDE.md                  — Sub-project instructions
├── rh_exploration.md          — Living exploration log
├── lib/
│   └── rh_core.py             — GUE analysis, spectral zeta, gap
├── experiments/
│   ├── EXP_071_rh_chain.py    — β=2, δ(N), Ramanujan, chain (11/11 ✓)
│   ├── EXP_071b_phase_structure.py — Phase extraction, interference (6/7 ✓)
│   └── EXP_071c_clt_boundary.py   — CLT boundary σ=1/2 (6/6 ✓)
├── theory/
│   ├── mobius_randomness.md    — KEY: formal conjecture document
│   ├── clt_boundary.tex        — Why Re(s)=1/2 (CLT proof)
│   ├── self_contradiction.tex  — δ(N) > 0 theorem
│   ├── z_n_definition.tex      — Z_N(s) definition
│   ├── continuous_geometry.tex — E_N → M as asymptotic
│   ├── induction_spectral_series.tex — Induction = ζ(s) partial sum
│   └── discrete_calculus.tex   — Calculus = add/subtract on G
├── results/                    — Experiment outputs
└── figures/                    — Plots
```

## Key Files

| File | Role |
|------|------|
| `theory/mobius_randomness.md` | **Master document** — formal chain, 7 theorems + 1 conjecture |
| `rh_exploration.md` | Living log with raw intuitions and history |
| `CLAUDE.md` | Sub-project instructions and API |

## Workflow

### When user uploads a new document about RH:
1. Move to `critical-line/theory/` (or appropriate subdir)
2. Read and identify: new theorems, new conjectures, new open problems
3. Update `rh_exploration.md` with new findings
4. If numerically testable → create EXP_071x experiment
5. Update `theory/mobius_randomness.md` if chain is extended

### When user asks to explore an open problem:
1. Read `theory/mobius_randomness.md` Section 8 (Open Problems)
2. Read `rh_exploration.md` for latest status
3. Design experiment or formal analysis
4. Run in `critical-line/experiments/`
5. Record results and update documents

### When user asks "RH 해줘" or similar:
1. Read `critical-line/HANDOFF.md` for latest session context
2. Read `critical-line/CLAUDE.md` for full status
3. Read `theory/Doubly_Irreducible.md` (keystone)
4. Identify the most promising open problem
5. Work on it (experiment + theory)
6. Update HANDOFF.md when done

## Key Numerical Results (reference)

| Test | Result | Experiment |
|------|--------|-----------|
| β=2 from ℂ | ⟨r⟩=0.594 (GUE=0.603) | EXP_071 |
| ℂ vs ℝ | ℂ→GUE, ℝ→GOE | EXP_071 |
| δ(N) scaling | 1.12·N^{-0.505}, R²=0.9992 | EXP_071 |
| Phase uniform | KS p=0.258, R=0.008 | EXP_071b |
| Phase entropy | ℂ=98.3%, ℝ=19.3% | EXP_071b |
| CLT |S_N|~√N | ratio=0.896 (theory 0.886) | EXP_071c |
| σ_geom(ℂ)=0.5 | exact within 0.05% | EXP_071d |
| Graph-PNT | C/C_theory=1.14 | EXP_071e |
| Born Ramanujan | 100% N≤200 (d=5) | EXP_071f |
| d_c ≈ 3 | ratio~1.94·d^{-0.67} | EXP_071g |
| N_c(5) ≈ 500 | ratio→1.135 asymptotic | EXP_071g |

## Open Problems (priority order)

1. ~~Functional equation's 1/2~~ → RESOLVED (Doubly_Irreducible.md §Resolution)
2. **Primitive path ↔ prime correspondence**
   Define "primitive paths" on simplex network → PNT
3. **Phase-to-Möbius map**
   Explicit map from Gram phases → μ(n), preserving multiplicativity
4. **Multiplicative structure**
   Euler product ζ(s) = Π(1-p^{-s})^{-1} imposes dependence. Does σ_stat = σ_geom survive?
5. **Beyond iid**
   Gram phases are structured, not iid. Show boundary still 1/2
6. **Higher L-functions**
   Dirichlet characters χ(n) ∈ U(ℂ) → GRH has same structural origin?

## Status Markers

Always maintain these distinctions:
- **Theorem**: proven result (reference Paper/EXP)
- **Conjecture**: formalized but unproven (Section 5.3 of mobius_randomness.md)
- **Observation**: numerically confirmed but not formalized
- **Poetry**: raw intuition, may not survive formalization

## Running Experiments

```bash
cd critical-line/experiments
python EXP_071_rh_chain.py               # 11/11
python EXP_071b_phase_structure.py       # 6/7
python EXP_071c_clt_boundary.py          # 6/6
python EXP_071d_two_boundaries.py        # 5/5
python EXP_071e_ihara_zeta.py            # 5/5
python EXP_071f_born_weight_ramanujan.py # 4/5
python EXP_071g_d_dependence.py          # 5/5
```

Total: 42/44 checks passed. Next available: EXP_071h

## Paper
`papers/paper5_critical_line.tex` — full results

## Edit Rules

- Small chunks only (Edit tool, never full rewrite)
- Always specify theorem/conjecture/observation status
- Cross-reference experiments: "EXP_071b confirms..."
- Author: "Mingu Jeong and Claude (Anthropic)"
