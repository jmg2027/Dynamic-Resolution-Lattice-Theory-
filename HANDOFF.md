# Session Handoff — 2026-04-14 (Session 3)

## Branch
`main` (all merged, all pushed)

## What Was Done

### SM Open Problems — ALL 5 RESOLVED
1. **Higgs λ** (EXP_071/072): face-level BC + embedding → m_H=125.28 (+0.02%)
2. **Δm_np** (EXP_073): S₂/S∞ → (1-S₂/S∞) = EM excess → 1.275 MeV (-1.5%)
3. **1/α₂** : phantom problem (ch08 already gives 30→29.6)
4. **ν ratio** (EXP_074): T₂₃=1/2+3/(2π²) → m₃/m₂=5.71 (+0.04%)
5. **1st gen quarks** (EXP_075): Ξ_conf=α/(d²-1), EM terms vanish → preserved

### Repo Reorganization
- `standard-model/` sub-project created (like rh-connection/)
- Root CLAUDE.md restructured hierarchically
- `correction_recipes.md` — practical reference for correction patterns

## Sub-Projects
```
standard-model/  ← SM corrections (EXP_071-075), RESOLVED
rh-connection/   ← RH exploration (separate branch)
atoms/           ← NEXT: periodic table, IE, chemistry
```

## Next Direction
Atomic physics / periodic table. The SM is closed.
Available experiment number: EXP_076.

## File Map
```
standard-model/CLAUDE.md               ← SM context
standard-model/correction_recipes.md   ← correction patterns
standard-model/experiments/EXP_071-075 ← SM experiments
CLAUDE.md                              ← hierarchical root
HANDOFF.md                             ← this file
```
