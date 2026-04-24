# 49 — Euclidean step 완전 증명 (L_m + L_k → L_{m-k})

## 결과

`Research/ModJoinEuclidean.lean`:

**`euclidean_step`** (0 sorry, 0 axiom):

```
theorem euclidean_step {α : Type} (N : Lens α) (m k : Nat)
    (hk : k ≥ 2) (hmk : m > k) (hdiff : m - k ≥ 2)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    (leavesModNat (m - k)).refines N
```

즉 **m > k ≥ 2 이고 m - k ≥ 2 이면 L_m.refines N ∧ L_k.refines
N → L_{m-k}.refines N**.

이것이 Euclidean algorithm 의 한 step 을 Lens refinement 수준
에서 실현.

## 구조

1. `leavesModNat` view 로 환원 → `r.leaves % (m-k) = r'.leaves
   % (m-k)` 획득.
2. **핵심 arithmetic lemma** (`key`):
   ```
   a % d = b % d → b ≤ a → a = b + ((a - b) / d) * d
   ```
   d = m - k > 0.  증명은 Nat.div_add_mod + mul_le_mul_left +
   Nat.mul_succ 로 b/d ≤ a/d 확립 후 mul_sub_distrib 로 조립.
3. `step_plus_nd` (ModJoinBezout 의 반복 chain_step_sub) 로
   n = (a - b) / (m-k) 만큼의 +d step chain.
4. `rcases` 로 r.leaves ≤ r'.leaves vs 반대 양분.

## Bezout chain vs Euclidean step

두 접근의 대조:

- **ModJoinBezout.consecutive_refines_const**: m = k + 1 일 때
  L_{k+1} + L_k → constant (gcd = 1 극한).
- **ModJoinEuclidean.euclidean_step**: 일반 m > k 일 때
  L_m + L_k → L_{m-k}.  m - k = gcd(m, k) 아닐 수도 있음.

Euclidean 한 step 은 "빼기" 하나.  gcd 까지 가려면 iterate:
(m, k) → (m-k, k) → ... Euclidean algorithm.  각 step 이
lemma 로 확보됐으므로 **finite iteration 으로 임의 (m, k)
에서 gcd(m, k) 도달**.

단, gcd(m, k) = 1 인 경우 (m-k, k) 가 최종이 (1, 1) 이 아니라
(1, k) 이므로 consecutive_refines_const 로 이행하려면 좀 더
정교한 iteration 관리 필요.  이는 별도 작업.

## 의의

**"Bezout chain 패턴은 확립됐으나 일반 m, k 는 미완"**
(note 46) 의 한 축 해소.

- Euclidean step 자체는 이제 형식화됨.
- 각 specific (m, k) pair 에 대한 join = L_gcd(m,k) 증명은
  이 step 을 iterate 하면 구성 가능.
- 일반 m, k 의 uniform theorem (induction on 모든 pair) 은
  아직 미완 — iteration bookkeeping 필요.

**"Join = gcd" 의 구조적 증명이 Lean 수준 iteration 을
제외하면 완료**.

## 남은 것

- General `join_eq_gcd` theorem (임의 m, k).  위 Euclidean
  step 을 바탕으로 strong induction + termination 증명.
- Join 의 concrete Lens 구성 은 여전히 open (note 48).
  단, mod family 의 specific 경우 각 L_gcd(m,k) 는 이미 정의
  돼 있으므로 해당 케이스는 완결.

## 변경 이력

- 2026-04-24: euclidean_step 완전 증명.  Bezout chain arc 의
  기술적 핵심 lemma.
