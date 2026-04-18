# Grand Picture — Gaps Register

Living document. Each gap tagged with:
- **Status**: open / in-progress / closed
- **Type**: Structural / Parameter / Numerical / Tested / External
- **Priority**: decisive (unblocks multiple) / useful / cosmetic
- **Blocker**: what must finish first
- **Next step**: minimal next experiment

## Active gaps

| ID | Short | Status | Type | Priority | Blocker | Next step |
|----|---|---|---|---|---|---|
| G1 | Map 1→3 (3,3)-ambient 정당화 | open | Structural | useful | — | ch04 §4.10-4.12 재독 |
| G2 | Level 5 family canonical d | open | Parameter | useful | G4 | — |
| G3 | Level 6 ↔ 1-4 일반 map | open | Structural | cosmetic | — | Plücker at each n 체크 |
| G4 | ε₀ 제1원리 도출 | open | Parameter | **decisive** | — | 변분 config det 편차 분석 |
| N1 | Regge S_var=56.79, S_sym=41.94 | refined | Numerical | useful | — | S ≠ 1/α_GUT. 무슨 identity인지? |
| N2 | (1/4)^4 ≈ ε₀ (지수 4) | open | Numerical | cosmetic | G4 | — |
| N3 | δ_AAA = π 재현 | **closed** | Numerical | — | — | FND_004 재현 확인 완료 |
| N4 | w² ≈ (3/2)α_GUT = 9/(25π²) | **new** | Numerical | useful | — | 변분 극값 해석 유도 |
| T1 | "2.4% = α_GUT universal" | closed | Tested | — | — | 기각됨 (FND_014) |
| T2 | 1-param Regge δ_AAA | closed | Tested | — | — | FND_019 wrong family |
| E1 | EXP-047b (δ_AAA=π 원본) | **closed** | External | — | — | = FND_004, 확인됨 |
| E2 | ch10 f_occ theorem 정밀도 | open | External | useful | — | 수치 크로스체크 |

## Dependency DAG (updated after E1/N3 closed)

```
E1 ✓ ──→ N3 ✓ ──→ N1 (refined)
                    ↓
G4 ←── N4 (new lead) ← 변분 극값
G2 ← G4

G1 (ch04 독립)
G3 (독립, cosmetic)
N2 (G4 해결시 자연히)
```

## Session progress (this round)

- **E1 closed**: EXP-047b = FND_004, 재현됨
- **N3 closed**: δ_AAA = π at variational 확인 (w=0.190, θ=45°)
- **N1 refined**: S_regge_variational = 56.79 ≠ 1/α_GUT = 41.12
  (내 이전 "S = 1/α_GUT" 추측은 틀렸음)
- **N4 new**: w² ≈ 9/(25π²) = (3/2)α_GUT at 0.8% - 새 numerical lead

## Recommended next

1. **N4 파고**: w² = 9/(25π²) 해석적 유도 시도 (변분 극값 조건에서 직접)
2. **G4 공격**: ε₀ = det(SSS) 편차 또는 det(SST) 편차에서 나오는지
   - det(SSS) = 0.905, 편차 0.095 = 1 - (1 - 3w² + 2w³) ~ 3w²
   - det(SST) = 0.964, 편차 0.036 = w²
   - ε₀ ≈ 0.0038 vs w² = 0.0362: 인수 10 차이
3. G1 병렬: ch04 ambient (나중)

