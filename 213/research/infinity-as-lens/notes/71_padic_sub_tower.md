# 71 — p-adic ℤ_p as leavesModNat sub-tower

`Research/Padic.lean` 형식화.  `ProfiniteSeq` (factorial seq +
leavesModNat 전체 family) 의 sub-tower 로 ℤ_p 실현.

## 핵심 구조

```
padicFamily p : Nat → Lens Nat
padicFamily p k = leavesModNat (p^(k+1))
```

- 모듈러스 가 항상 ≥ p ≥ 2.
- p prime: standard ℤ_p.
- p general (≥ 2): mod-p^k tower (CRT-decomposable).

## 결과

1. `padic_family_cauchy`: factorial seq Cauchy w.r.t. 각 level.
2. `padic_family_limit_zero`: limit class = 0 at each level.
3. `padic_tower_refines`: level k+1 refines level k —
   canonical projection ℤ/p^(k+2) ↠ ℤ/p^(k+1).
4. `padic_familyCauchy`: family-Cauchy w.r.t. 전체 tower.
5. `padic_limit_all_zero`: limit assignment 이 identically 0
   (the p-adic zero of ℤ_p).

## Axiom 검증

`#print axioms` 결과:
- padic_family_cauchy: [propext, Quot.sound]
- padic_family_limit_zero: [propext, Quot.sound]
- padic_tower_refines: [propext]
- padic_familyCauchy: [propext, Quot.sound]
- padic_limit_all_zero: [propext, Quot.sound]

Classical.choice / LEM / native_decide 부재.  Lean 4 core
baseline (propext + Quot.sound) 만.  AXIOM §5.2.1 falsifiability
유지.

## 의의

ℤ_p 는 표준 number theory 의 무거운 도구.  213 framework 에서
는 leavesModNat sub-family + factorial seq 만으로 자연스럽게
realized — **추가 공리 0**.

`ProfiniteSeq` (Ẑ = ∏_p ℤ_p) 의 sub-tower 로서, p 별 ℤ_p 는
factorial seq 라는 **하나의 공통 source** 로부터 분리됨.
원소론 적으로 보면:

- factorial(n+1) ≡ 0 (mod p^k) for n+1 ≥ p^k (실은 더 약한
  조건도 충분).  →  각 ℤ_p 의 0 element.
- 모든 prime p 에서 동시에 0 →  Ẑ 의 0 element.
- CRT decomposition 의 213-side 표현.

## 기존 결과 와의 관계

- 67_profinite_factorial_limit.md: factorial seq + 전체 mod
  family.  Ẑ scope.
- 71 (이 note): 같은 factorial seq 의 single-prime restriction.
  ℤ_p scope.

따라서 71 은 67 의 **specialization** 이고 새로운 forcing 이나
tool 추가 없음 — 단지 sub-family 로 절단.  하지만 number-theoretic
완전성 의 표현 으로 가치 있음 (Ẑ ≃ ∏_p ℤ_p 는 number theory 의
기본 사실).

## 변경 이력

- 2026-04-25: Padic.lean 작성.  ProfiniteSeq 위에 sub-tower
  layer.  5 결과 모두 propext+Quot.sound only.
