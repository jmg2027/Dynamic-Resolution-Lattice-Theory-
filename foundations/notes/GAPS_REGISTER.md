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
| G-M_i | M_i 기하 유도 | **refuted (direct+deficit)** | Parameter | decisive | 깊은 수학 | FND_035+036: 모든 hinge-level route 기각. Book 값 fit 확정. |
| N1 | Regge S_var=56.79, S_sym=41.94 | refined | Numerical | useful | — | S ≠ 1/α_GUT. 무슨 identity인지? |
| N2 | (1/4)^4 ≈ ε₀ (지수 4) | open | Numerical | cosmetic | G4 | — |
| N3 | δ_AAA = π 재현 | **closed** | Numerical | — | — | FND_004 재현 확인 완료 |
| N4 | w² ≈ (3/2)α_GUT = 9/(25π²) | **refuted** | Numerical | — | — | 0.4% off, gap > 수렴 정밀도 |
| T1 | "2.4% = α_GUT universal" | closed | Tested | — | — | 기각됨 (FND_014) |
| T2 | 1-param Regge δ_AAA | closed | Tested | — | — | FND_019 wrong family |
| E1 | EXP-047b (δ_AAA=π 원본) | **closed** | External | — | — | = FND_004, 확인됨 |
| E2 | ch10 f_occ theorem 정밀도 | open | External | useful | — | 수치 크로스체크 |

## Updates (FND_036, 2026-04-18)

- **Regge deficit 루트도 REFUTED**. 9가지 aggregate 시도, 최저
  total deviation **198.3%** (1/Σa). 깔끔한 기하 derivation 없음.
  - 테스트한 후보: Σa, Σδ, Σ(aδ), 평균, c^k 가중, 1/Σ.
  - 흥미로운 발견:
    - AAA dihedral = π/4 (입력 θ와 수치 일치)
    - AAB dihedral = π/2 (블록 orthogonal 필연)
    - ABB dihedral = 1.4103 rad
    - M/gauge ≈ {55/32, 7/4, 1/3}: Strong·Weak 근사 일치(1.8%)
      but EM 다름. 깔끔한 rational 패턴 없음.
- **강한 결론**: (3,2) hinge 기하의 **직접적** 측정으로는 book M_i
  유도 불가. Book 값은 관측 Δ_i에서 역산된 fit value로 확정.
- **심각성 확대**: "0 free parameter" 주장에 숨은 자리 확정 3개.
  - 수학이 정말로 익어야 풀릴 문제. Schubert/Fulton-MacPherson /
    Binet-Cauchy exponents 같은 **더 깊은 구조** 필요.
  - 현재 도구로는 접근 불가 → Phase A' 일시 중단.

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

## Dependency DAG (updated after FND_034/035/036)

```
E1 ✓ ──→ N3 ✓ ──→ N1 (refined, stalled)
                     ↓
G4 (refined, blocked by W4)
G-M_i (refuted direct+deficit, blocked by W1/W2/W3)

W1─┐
W2─┼─→ G-M_i → 핵물리 a_V,a_S,a_C 오차 <1% 가능
W3─┘

W4 → G4 closed → N2 자연히
W5 → 4D machine-verified (Lean overclaim 해소)

G1, G3: 독립, cosmetic
```

## Session progress (2026-04-18)

- **FND_034**: ε₀ = α_GUT/(2π) strict identity **refuted** at 2.6%.
  Leading 1/(2π) factor 97% 유효, residual (α_GUT/π)² order.
  c1=0.974 구조 correction 미해명.
- **FND_035**: M_i = Σ√det(G_h) per class **refuted**. 순서 완전 반대.
  Book M_i 는 관측 Δ_i 에서 역산된 fit value 확정.
- **FND_036**: M_i Regge deficit 9 routes **refuted**. 최저 198%.
- **누적 결론**: weight layer (W1–W5) 수학 성숙 필요. 현 hinge-level
  도구 한계 도달. 사용자 가설 "물리 오차 = 수학 미성숙" 확정.

## 수학 트랙 TODO (weight layer)

Session B가 **count layer** 완료:
- Gr(3,5) Schubert cell count = 10
- Binet–Cauchy 1+12+12 = 25
- FM cohomology χ = 5^N·(N+1)!
- n=5 unique alive decomposition

그러나 물리 M_i / ε₀ 유도 위해 **weight layer** 필요. 수학 트랙이
풀어야 할 5가지:

| ID | 이름 | 현황 | 필요한 것 | 목표 |
|----|------|------|-----------|------|
| W1 | Schubert weights on Gr(3,5) | count only | Pieri chain + SU(3)×SU(2) branching | cell별 canonical weight |
| W2 | FM equivariant cohomology | χ pattern only | class별 weight decomposition | AAA/AAB/ABB → M_i |
| W3 | Binet–Cauchy fiber weight | 1+12+12 count only | equivariant refinement (fiber weight) | channel별 weight |
| W4 | Regge closed form (ε₀) | FND_034 residual | c1=0.974 structural derivation | ε₀ exact |
| W5 | n=5 → 4D forcing | Lean definitional | γ'-operator argument (FND_033) Lean | 4D machine-verified |

**의미**: 이 중 **어느 하나라도** 풀리면 물리 트랙이 다음 단계
가능. 특히 W1/W2/W3 중 하나 → G-M_i 해결 → 핵물리 a_V,a_S,a_C
오차 3-7% → <1%. W4 → G4 완전 해결. W5 → Lean overclaim 해소.

**현 위치**: 물리 트랙 내에서 FND_037+ 더 돌려도 큰 진전 없음
(FND_034/035/036에서 이미 확인). 수학 성숙 대기.

