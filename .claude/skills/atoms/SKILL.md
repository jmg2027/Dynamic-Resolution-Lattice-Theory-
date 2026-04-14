---
name: atoms
description: "Atomic physics and periodic table from simplex geometry. Triggered by: 'atom', '원자', 'periodic', '주기율', 'ionization', 'IE', 'screening', '차폐', 'shell', 'orbital', 'element', '원소'."
---

# Atoms Skill

Manage atomic physics sub-project. Pure simplex geometry only.

**Working directory:** `atoms/`

## Rules
1. **NO Z_eff, Slater, Aufbau, orbital labels** — derive from geometry
2. Screening = trace conservation on simplex
3. Shell structure must EMERGE from δS/δψ=0

## Screening Constants (all from d=5)
```
σ_1s     = 1-n_S/(d²-1)    = 7/8
σ_same_s = 1/n_T+c²α       = 0.597
σ_2s→2p  = 1-n_S/(d(d-1))  = 17/20
σ_3s→3p  = 1-n_T/(d(d-1))  = 9/10
σ_same_p = n_S/(d-1) [n=2], n_T/n_S [n=3]
Δ_pair   = n_S/π²           = 3/π²
```

## Current Precision
Period 1-2: ALL <3%. Period 3: <10%. Z=1-118: 58% <30%.

## When triggered
1. Read `atoms/HANDOFF.md` first
2. New experiments go in `atoms/experiments/`
3. Results go in `atoms/results/`
