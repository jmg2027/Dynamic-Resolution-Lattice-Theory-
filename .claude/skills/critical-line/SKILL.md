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
├── HANDOFF.md                 — Session state
├── rh_exploration.md          — Living exploration log
├── lib/
│   └── rh_core.py             — GUE analysis, spectral zeta, gap
├── experiments/
│   ├── RH_001_rh_chain.py     — β=2, δ(N), Ramanujan, chain (11/11 ✓)
│   ├── RH_002_phase_structure.py — Phase extraction, interference (6/7 ✓)
│   ├── ...
│   └── RH_046_u_to_s_map.py   — u→s map graph-to-Riemann
├── theory/
│   ├── Doubly_Irreducible.md   — KEY: why 2 is unique
│   ├── zeta2_unification.md    — All π from Σ1/n²
│   ├── finite_incompleteness.md — Paper 7 basis
│   ├── ym_rh_parallel.md       — YM-RH connection
│   └── (15+ theory docs)
├── lean/
│   └── CriticalLine/           — Lean 4 formalization (~65 theorems)
└── results/                    — Experiment outputs
```

## Key Numerical Results

| Test | Result | Experiment |
|------|--------|-----------|
| β=2 from ℂ | ⟨r⟩=0.594 (GUE=0.603) | RH_001 |
| ℂ vs ℝ | ℂ→GUE, ℝ→GOE | RH_001 |
| δ(N) scaling | 1.12·N^{-0.505}, R²=0.9992 | RH_001 |
| Phase uniform | KS p=0.258, R=0.008 | RH_002 |
| CLT |S_N|~√N | ratio=0.896 (theory 0.886) | RH_003 |
| σ_geom(ℂ)=0.5 | exact within 0.05% | RH_004 |
| Graph-PNT | C/C_theory=1.14 | RH_005 |
| Born Ramanujan | 100% N≤200 (d=5) | RH_006 |
| d_c ≈ 3 | ratio~1.94·d^{-0.67} | RH_007 |
| PNT from Z[i] | no reals needed | RH_039 |
| Möbius from cycles | pi(p²)%pi(p)=0 | RH_042 |
| u→s map | Ramanujan=RH under u=q^{-s} | RH_046 |

## Open Problems (priority order)

1. ~~Functional equation's 1/2~~ → RESOLVED (Doubly_Irreducible.md)
2. **Primitive path ↔ prime correspondence** → PNT
3. **Phase-to-Möbius map** → explicit map Gram phases → μ(n)
4. **Multiplicative structure** → Euler product
5. **Higher L-functions** → GRH

## Status

46 experiments (RH_001-046). ~65 Lean theorems (0 sorry). Paper 7 written.
Next available: RH_047.

## Edit Rules

- Small chunks only (Edit tool, never full rewrite)
- Always specify theorem/conjecture/observation status
- Cross-reference experiments: "RH_001 confirms..."
- Author: "Mingu Jeong and Claude (Anthropic)"
