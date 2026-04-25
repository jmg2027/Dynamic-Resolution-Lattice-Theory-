# 67 — Profinite Cauchy instance: factorial seq → Ẑ-zero

Mingu (b) 제안 의 형식 demonstration.

## 결과

`Research/ProfiniteSeq.lean`:

**factorial seq xs (with leaves(xs n) = factorial(n+1))** 가
leavesModNat family 전체 에 대해 family-Cauchy.  Limit assignment
가 **모든 m 에 대해 0** — Ẑ (profinite ℤ) 의 zero element 와
정확히 대응.

## 형식 정리

- `factorial`, `factorial_pos`, `factorial_dvd`: factorial 함수
  정의 + 기본 성질.
- `factorial_eventually_zero_mod`: n + 1 ≥ m → factorial(n+1) %
  m = 0.
- `factorial_seq_cauchy`: leavesModNat m Cauchy.
- `factorial_seq_limit_zero`: limit class = 0 mod m.
- `leavesModNatFamily`: family indexed by {m : ℕ // m ≥ 2}.
- `factorial_seq_familyCauchy`: family-Cauchy.
- `factorial_seq_limit_all_zero`: 모든 m 에 대해 limit = 0.

## 213 → Ẑ 대응

| Profinite ℤ | 213 |
|------------|-----|
| Profinite zero (0 ∈ Ẑ) | factorial seq 의 limit assignment |
| 각 mod m residue | leavesModNat m view |
| Cauchy in profinite topology | family-Cauchy w.r.t. leavesModNat family |
| Limit space Ẑ | iProdLens leavesModNatFamily 의 image |

이게 정확히 ℕ → Ẑ embedding 의 213 reduce.

## 의의

213 framework 가 단순 finite combinatorics 가 아니라 **algebraic
profinite structure** 를 자연스럽게 생성:

- Limit 이 새 Raw 부재 (factorial(n+1) 자체 는 Raw, 하지만 limit
  은 lens output 0).
- 외부 metric 부재 — leavesModNat family 의 indexed product 가
  profinite topology 대체.
- Q37.3 (universalLens) + Cauchy completeness (limitLens) 가
  통합 framework.

profinite 수론 의 213 reduce 의 첫 explicit instance.  Ẑ-style
limit 이 213 안에서 자연스럽게 도출.

## 다음 work 가능

- p-adic ℤ_p instance: leavesModNat (p^k) family.
- ℝ-like instance: 더 복잡한 family (Archimedean).
- Algebraic operation (+ in Ẑ) 의 213 표현.

## 변경 이력

- 2026-04-25: factorial seq 의 profinite Cauchy + limit zero.
  Mingu 통찰 (b) 의 explicit instance.
