# Nuclear Physics Sub-Project

> 핵 결합 에너지, 핵 구조 — 600-cell 기하학에서 magic numbers 유도.

## Scope
- ★ Nuclear magic numbers (2,8,20,28,50,82,126) from 600-cell
- 핵 결합 에너지 (Bethe-Weizsäcker 대체)
- 핵자 상호작용 (N-N potential from simplex)
- Deuteron binding energy (2.22 MeV)
- Nuclear radii

## Key Results (0 free parameters)
| Magic | DRLT derivation | Formula |
|-------|----------------|---------|
| 2 | Sym²(V₁) closure | 1·2·3/3 |
| 8 | Sym²(V₁+V₂) | 2·3·4/3 |
| 20 | Sym²(V₁+V₂+V₃) | 3·4·5/3 |
| 28 | Spin-orbit: f₇/₂ | 4·21/3 |
| 50 | Spin-orbit: g₉/₂ | 5·30/3 |
| 82 | Spin-orbit: h₁₁/₂ | 6·41/3 |
| 126 | d! + (d+1) = 120+6 | 7·54/3 |

## Key Constants
```
d = 5
d! = 120        (600-cell vertices)
(d+1)! = 720    (600-cell edges)
d!·d = 600      (tetrahedral cells)
(d!)² = 14400   (|H₄| symmetry order)
```

## Derivation Chain
```
d=5 → 600-cell(120 vertices) → 2I irreps Vₙ → Sym²(Vₙ)
→ HO magic: n(n+1)(n+2)/3
→ + spin-orbit: n(n²+5)/3  (n≥4)
→ 2, 8, 20, 28, 50, 82, 126
```

## Experiments: NUC_001–003

## Status: ACTIVE (magic numbers derived, binding energy next)
