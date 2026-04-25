# 68 — ℝ-like Archimedean: Dedekind cut via abLens + order projection

Mingu (C) 방향 (2026-04-25) 의 형식 demonstration 시작.

## 핵심 design (Mingu)

| 역할 | 213 구현 |
|------|---------|
| Lens core (fold-structured) | `abLens : Lens (Nat × Nat)` |
| Order discriminator | `orderProj m k (a, b) := decide (a*k ≤ b*m)` |
| Cauchy 조건 | 모든 (m, k) 에 대해 eventually constant |
| Limit | Dedekind cut: 일관 된 decision function |
| Archimedean | (m, k) ∈ ℕ × ℕ⁺ 가 ℚ⁺ dense |

## 형식 결과 (Research/ArchimedeanCauchy.lean)

### 기초

- `orderProj`: cross-multiplication 형 비교.
- `isOrderCauchy`: family-Cauchy.
- `OrderCauchyData`: explicit witness 구조.
- `OrderCauchyData.cut`: Dedekind cut.

### Diagonal sequence (a = b = n+1)

- `diagonal_seq_orderProj_const`: orderProj n-independent.
- `diagonal_seq_orderCauchy`: trivially Cauchy (constant).
- `diagonal_seq_cut`: cut = decide (k ≤ m) = ratio 1.

### Ratio-one-from-below (a = n+1, b = n+2)

- `ratio_one_below_orderProj_eventually`: (m, k) 별 N 다름.
- `ratio_one_below_orderCauchy`: Cauchy.
- `ratio_one_below_cut_eq_diagonal`: 같은 cut = ratio 1.

이게 ℝ 의 quotient 의 213 reduce: 다른 sequence, 같은 limit.

## 의의

### Limit 이 Lens output 의 decision function

ℝ-element 가:
- 새 Raw 부재 (Raw 는 finite-depth).
- 새 Lens 구성 부재 (orderProj family 만 사용).
- **Lens output (Bool family) 의 일관 된 assignment**.

즉 ℝ 가 213 안 에서 "Raw 의 Lens-output 에 대한 ordering decision".

### Archimedean property 자동

(m, k) ∈ ℕ × ℕ⁺ family 가 ℚ⁺ dense.  임의 두 reference 사이
또 reference 존재.  ε > 0 = "specific (m, k)" 의 213 reform.

ε → 0 = (m, k) ratio refinement 의 limit.

### 외부 metric 부재

전통: ℚ 위 |·| metric → Cauchy → ℝ.
213: abLens + order projection family → cut → ℝ-element.

같은 결과, 외부 도구 부재.

## Paper 1 의 climax 통합

이로써 213 framework 가:
- Q37.3 (universalLens for arbitrary slash-cong).
- Cauchy completeness (limitLens via universalLens).
- Profinite limit (Ẑ-zero via factorial seq).
- Archimedean completion (ℝ-element via Dedekind cut).

모두 단일 framework 에서 자연 도출.

## 다음 work

- More instances: ratio 1/2, π-like irrational approximation.
- Algebraic operations on cuts: + via cut combination.
- Universal property: cut 이 "least sequence-collapsing" Lens.

## 변경 이력

- 2026-04-25: ℝ-like Dedekind cut via abLens + orderProj.
