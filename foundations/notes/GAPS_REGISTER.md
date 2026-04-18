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
| G4 | ε₀ 제1원리 도출 | **refined** | Parameter | useful | G-M_i | FND_034: α_GUT/(2π) refuted at 2.6% |
| G-M_i | M_i 기하 유도 | **refuted (direct)** | Parameter | decisive | 다른 기하 구조 | FND_035: Σ√det 경로 기각. Book 값은 fit. |
| N1 | Regge S_var=56.79, S_sym=41.94 | refined | Numerical | useful | — | S ≠ 1/α_GUT. 무슨 identity인지? |
| N2 | (1/4)^4 ≈ ε₀ (지수 4) | open | Numerical | cosmetic | G4 | — |
| N3 | δ_AAA = π 재현 | **closed** | Numerical | — | — | FND_004 재현 확인 완료 |
| N4 | w² ≈ (3/2)α_GUT = 9/(25π²) | **refuted** | Numerical | — | — | 0.4% off, gap > 수렴 정밀도 |
| T1 | "2.4% = α_GUT universal" | closed | Tested | — | — | 기각됨 (FND_014) |
| T2 | 1-param Regge δ_AAA | closed | Tested | — | — | FND_019 wrong family |
| E1 | EXP-047b (δ_AAA=π 원본) | **closed** | External | — | — | = FND_004, 확인됨 |
| E2 | ch10 f_occ theorem 정밀도 | open | External | useful | — | 수치 크로스체크 |

## Updates (FND_035, 2026-04-18)

- **G-M_i 직접접근 REFUTED**: M_i = Σ√det(G_h) per class 안 맞음.
  - 기하: Σvol(AAA)=0.951, Σvol(AAB)=5.890, Σvol(ABB)=2.121
    (per-hinge avg: {0.95, 0.98, 0.71})
  - Book M_i: {13.75, 1.0, 3.5} → 순서가 **완전 반대**
  - w vs w₀ 차이 무관 (M_i는 topology 의존, 변분 세부 아님)
- **Empirical extraction matches book** (빈 자리 메우기):
  - Strong: 0.47/(8·0.0038) = 15.46 vs 13.75 (12%)
  - Weak: 0.40/(30·0.0038) = 3.51 vs 3.5 ✓ (perfect)
  - EM: 0.22/(59.22·0.0038) = 0.978 vs 1.0 (2%)
- **의미 deep**: Book M_i 는 관측 Δ_i 에서 역산된 **fit value**.
  "M_i는 (n_A, n_B) topology에서 결정되는 기하 가중치"라는 ch12
  주장은 aspirational이고 실제 유도는 없음. 0-parameter 주장에
  숨은 자리 3개 (M_Strong, M_Weak, M_EM).
- **다음 route**: Regge deficit-based weight `a·(2π−Σθ)` per class,
  또는 Binet-Cauchy exponent 조합 (c^k·C(n_A,3−k)·C(n_B,k)).
- **Priority 재평가**: G-M_i는 decisive지만 직접 경로 닫힘.
  순수 수학 더 익어야 풀릴 수준. 다른 gap과 순서 조정 필요.

## Updates (FND_034, 2026-04-18)

- **G4 refined**: ε₀ = α_GUT/(2π) conjecture tested to 4 digits.
  - w* (Brent, tol 1e-14, bracket 0.1/0.2/0.3) = 0.19026442
  - ε₀_eff via Identity A `w*² = (3/2)α_GUT(1−2ε₀)` = **0.003778**
  - α_GUT/(2π) conjecture = 0.003870
  - Deviation: **-2.57%** (exact identity REFUTED)
- **Identity B survives**: `w*² = (3/2)α_GUT·(1 − α_GUT/π)` holds
  at residual +7.26e-6, order (α_GUT/π)² = 6e-5.
  → Leading coefficient 1/(2π) is correct at 97%, but 2.6%
    structural correction c1 = 0.974 remains unexplained.
- **Implication**: FND_015의 2% 일치는 conjecture 유효성 아닌
  우연. 진짜 ε₀는 w*에서 0.003778. Book의 0.0038 (2 sig fig)에는
  양쪽 다 부합.
- **Priority shift**: G4 alone is NOT decisive. Blocker 진짜는
  **G-M_i** (기하 가중치) — M_i가 정확하지 않으면 Δ_i에서
  ε₀ 추출도 정밀하지 않음 (FND_015 Δ_i 비교 10-12% off).
  → **다음은 FND_035: M_i from Binet-Cauchy canonical weights**.

## Updates (FND_021)

- **N4 refuted**: w* (Brent, tol 1e-14) = 0.190264 vs 3/(5π) = 0.190986.
  Gap 0.38% > convergence tol → w² ≠ 9/(25π²) exactly.
  S(w*) > S(3/(5π)) detectably.
- **Coincidence**: gap ≈ ε₀ = 0.0038 itself. Could suggest
  w* = (3/(5π))(1-ε₀), but this is numerical loop, not proof.
- **G4 status**: w-based derivation path closed (N4 refuted).
  Need different geometric origin for ε₀.

## Dependency DAG (updated after E1/N3 closed, N4 refuted)

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

1. **FND_035: G-M_i 기하 가중치** (NEW PRIORITY)
   — Binet-Cauchy 1+12+12=25 채널 각각의 canonical weight를
     simplex metric에서 도출. 핵물리 a_V, a_S, a_C 3-7% 오차의 origin.
2. **G4 refinement**: c1 = 0.974 의 structural origin 규명.
   — α_GUT·exp(−α_GUT)/(2π) 후보, hinge angular integration path.
3. **N4**: w² = 9/(25π²) 해석적 유도 (G-M_i 풀리면 자연히)
4. G1 병렬: ch04 ambient (나중)

