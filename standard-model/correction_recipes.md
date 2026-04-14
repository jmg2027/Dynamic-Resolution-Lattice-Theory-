# Correction Recipes — 실험 참고용
> 이 세션 (2026-04-14)에서 발견한 보정 패턴.
> 새 실험/도출 시 체크리스트로 사용.

## 1. Binet-Cauchy 레벨 계층

sub-structure 크기 k에 따라 물리량이 달라진다:

| k | 구조 | BC 채널 | 물리 | 공식 |
|---|------|---------|------|------|
| 3 | Hinge | 1+12+12=25=d² | Gauge coupling | 1/α_i = C×g×S(N) |
| 4 | Face | 4+12=16 | Scalar coupling | λ = f²(1+2x)²/2 |
| 5 | Simplex | 12 (det) | det(G) | — |

**Face BC 공식:**
```
Λ⁴(ℂ⁵): k=0 (AAAA)=0, k=1 (AAAB)=C(3,3)C(2,1)c¹=4, k=2 (AABB)=C(3,2)C(2,2)c²=12
```

## 2. Scalar vs Fermion Dressing

**절대 혼동하지 말 것.** 이걸 틀리면 ~1% 급 오차 발생.

| 입자 유형 | Dressing | 공식 | 왜? |
|-----------|----------|------|-----|
| Fermion mass | Propagator P(x) | (1+2x)/(1+x) | 닫힌 루프 정규화 필요 |
| Scalar coupling | Vertex V(x) | 1+2x | potential = vertex, 루프 없음 |

```python
# x = α_GUT × f_occ
def fermion_dressing(x):   return (1 + 2*x) / (1 + x)  # P(x)
def scalar_dressing(x):    return 1 + 2*x                # V(x) = numerator of P
```

## 3. Simplex Embedding Correction

sub-structure가 simplex에 내장될 때, missing vertices로 coupling이 leak.

```
δ = α_GUT × (missing vertices) / d
corrected = bare × (1 - δ)
```

| 구조 | vertices | missing | δ | 적용 |
|------|----------|---------|---|------|
| Edge (2) | 2 | 3 | 3α/d | 미확인 |
| Hinge (3) | 3 | 2 | 2α/d | gauge Δ_i? |
| Face (4) | 4 | 1 | **α/d** | **Higgs ✓** |
| Simplex (5) | 5 | 0 | 0 | 보정 없음 |

**주의:** 이 보정은 face-level에서만 검증됨 (Higgs). 다른 레벨은 확인 필요.

## 4. EM Excess Fraction

EM과 weak가 거의 상쇄되는 양 (AAB=ABB=12)에서:

```
잘못된 것: S₂/S∞        (= weak의 EM 대비 비율 = 0.760)
올바른 것: 1 - S₂/S∞    (= EM이 weak 넘어 나가는 비율 = 0.240)
```

**규칙:** "차이"에 비례하는 양은 **(1-S₂/S∞)** 사용.
- Δm_np: isospin breaking = EM excess → (1-S₂/S∞) ✓
- 결합상수 자체 (1/α₂ = 12×2×S(2)): S(2) 직접 사용, 비율 아님

## 5. 내부 일관성 체크

새 공식 만들 때 반드시 확인:
1. **같은 챕터의 다른 표와 모순 없는가?** (ch09: 2.28 vs 2.505 사건)
2. **옛 공식이 이미 대체되지 않았는가?** (1/α₂: 옛 노트의 18.2 vs ch08의 30)
3. **DRLT 도출값 vs 관측값 중 어느 걸 쓰는가?** (DRLT 도출값 우선)

## 6. 수치 빠른 참조

```python
α_GUT = 6/(25π²) ≈ 0.024317
α_em  = 1/137.036
S(2)  = 5/4 = 1.25
S(∞)  = π²/6 ≈ 1.6449
S₂/S∞ = 15/(2π²) ≈ 0.7599
1-S₂/S∞ ≈ 0.2401
ε = α^(2/3)(1+α) ≈ 0.08597
c = 2, d = 5, n_S = 3, n_T = 2
v_H = 6·M_Pl/5²⁵ ≈ 245.80 GeV
```

## 7. 보정 적용 순서

1. **Bare value**: combinatorial formula (occupation fraction, channel count)
2. **Vertex/Propagator dressing**: scalar(1+2x) or fermion P(x)
3. **Embedding correction**: (1-α×miss/d) if sub-structure < simplex
4. **Ξ correction**: α_em/(1-α)+α/(d²-1)+α_em² (fermion masses only)
5. **det(G_h) correction**: Δ_i from trace conservation (gauge couplings)
