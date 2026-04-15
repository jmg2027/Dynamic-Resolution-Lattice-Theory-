# Atoms Handoff — 2026-04-15 (Final)

## 두 가지 성과

### A. Screening Model (ATM_018-022): median 3.5%
- 8개 screening 상수로 Z=1-118 전부 30% 이내
- 76(<5%), 111(<15%), 118(<30%), median 3.5%
- 패턴 매칭이지만 manifold 해석 있음

### B. Manifold Variational (ATM_024-025): δ(AAA) = π
- 올바른 기하: Δ⁴ (5꼭짓점, 3A+2B)
- 2-simplex gauge 연결 → δ(AAA) = π 정확히 도출
- IE(H) = Ry, IE(He) = 2Ry(1-4α_GUT)
- Li manifold: 4 simplices, screening = temporal 겹침

## Screening Constants (manifold 해석 포함)
```
Cross-pair (다른 심플렉스 쌍 → 공유 AAB 힌지):
  σ_cross = 1-n_S/(d²-1) = 7/8 = 0.875

Same-pair (같은 심플렉스 → Binet-Cauchy):
  σ_same_s = 1/n_T + c²α_GUT = 0.597

Subshell:
  σ_ns→np(even) = 1-n_S/(d(d-1)) = 17/20
  σ_ns→np(odd)  = 1-n_T/(d(d-1)) = 9/10
  σ_same_p(p=2) = n_S/(n_S+1) = 3/4
  σ_same_p(p≥3) = n_T/(n_T+1) = 2/3
  σ_df→p = 1-α_GUT = 0.976
  Δ_pair = n_S/π² = 3/π²
```

## 근본적 미해결: S_total
- Regge action → 기하학 (δ, shell 구조)
- Gram matrix → coupling (α, σ)
- 둘을 통합하는 S_total = S_Regge + S_matter 미정립
- 이것이 있으면 변분에서 screening이 도출 가능

## Experiment Map
```
ATM_014-016: He, screening analysis, Period 2 complete
ATM_017: Full periodic baseline (26.1%)
ATM_018: σ_core = 27/10 (6/6 ✓)
ATM_019: σ_df = 1-α_GUT (5/5 ✓)
ATM_020: Layered shell (4/4 ✓, 7.4%)
ATM_021: Filling fraction (4/4 ✓, 3.8%)
ATM_022: d-pair (4/4 ✓, 3.5%)
ATM_023: 폐기 (틀린 기하)
ATM_024: Δ⁴ single (5/5 ✓, δ=3π/2)
ATM_025: 2-simplex manifold (3/4 ✓, δ=π!!!)
Next: ATM_026
```
