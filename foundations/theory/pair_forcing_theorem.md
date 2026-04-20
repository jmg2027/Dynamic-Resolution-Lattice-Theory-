# Pair Forcing Theorem — (2, 3) 의 arithmetic 유일성

**Date:** 2026-04-19
**Lean status:** 미완 (closed-form proof 서술됨)
**FND ref:** FND_042 (L 일반화), FND_043 (coprime pair 전수)

---

## 정리

**Theorem (Pair Forcing).**  `A = {p, q}` (coprime, 2 ≤ p < q) 위에서
`n = p·c_p + q·c_q`, `(c_p, c_q) ∈ ℕ²` 의 decomposition 에 대해:

- *atomic(n)*: `n` 의 decomp 이 유일 AND 둘 다 odd positive

라 정의하자.  그러면 **atomic n 이 유일하게 존재하는 coprime pair
는 `(p, q) = (2, 3)` 뿐이고, 그 n = 5.**

---

## 증명 (closed form)

**Step 1 (Bézout shift 유일성 조건).**  gcd(p,q)=1 이므로
`(c_p, c_q) ↦ (c_p + q, c_q - p)` 는 `p·c_p + q·c_q` 를 보존.
ℕ² 에서 유일 decomp ⟺ `c_p < q` AND `c_q < p`.

**Step 2 (alive 조건).**  c_p, c_q 모두 odd positive.

**Step 3 (count 공식).**  atomic (c_p, c_q) 의 수
= |{c_p odd ∈ [1, q-1]}| · |{c_q odd ∈ [1, p-1]}|
= ⌊p/2⌋ · ⌊q/2⌋.

**Step 4 (유일성).**  count = 1 ⟺ ⌊p/2⌋ = 1 AND ⌊q/2⌋ = 1.
- ⌊k/2⌋ = 1 ⟺ k ∈ {2, 3}.
- p < q, coprime, 둘 다 ∈ {2, 3} → (p, q) = (2, 3).

**Step 5 (값).**  (c_p, c_q) = (1, 1) unique, n = 2·1 + 3·1 = 5.  ∎

---

## 의의

### 1. DRLT d=5 의 arithmetic 기원 강화

기존 213 framework 은:
- arity = 2 (ArityForcing)
- atoms = {2, 3} (non-decomposable ≥ 2)
- atomic n = 5 (Atomicity)

까지 각 step 을 independent lemma 로 증명.  **Pair Forcing Theorem
은 이 셋을 하나로 통합**:

> 모든 coprime 2-원소 atom set 중 **유일 atomic n 을 가지는
> set 은 {2, 3} 뿐**.

즉 "atomic n 유일" 조건 하나로:
- atom set 의 개수가 2 (pair)
- atom values 가 {2, 3}
- dimension n = 5

가 **동시에** 결정됨.

### 2. 일반화 불가능성

- **3-원소 이상**: atoms 가 3+ 개면 Bézout shift 가 다양해져
  atomic n 이 항상 empty (FND_042: L ≥ 3 → atomic ∅).
- **non-coprime**: gcd > 1 이면 n 이 gcd 배수로 제한되어
  "모든 ℕ" 에 대한 theory 불가.
- **alive 조건 변경**: "c_p, c_q 둘 다 odd" 는 Raw distinctness
  규칙의 직접 귀결 (PAPER §6.6(c)).  바꾸면 Raw 공리 위배.

### 3. 물리 해석

- (p, q) = (2, 3): Raw 의 두 가장 기본 cardinality
  - `p = 2`: base pair {o_0, o_1}
  - `q = 3`: {o_0, o_1, relation o_0 o_1} (첫 closure)
- n = 5: **unique dimension** 에서 두 atom 이 각각 1회씩 사용
- (c_p, c_q) = (1, 1): 공간 3 + 시간 2 의 partition 으로 대응
  (Corollary 6.4)

### 4. 따름정리

A = {p, q} coprime, 2 ≤ p < q 일 때:
- atomic n 수 = ⌊p/2⌋ · ⌊q/2⌋
- 이 수가 0 인 pair 는 없음 (모든 coprime pair 는 최소 1개 atomic n)
- 이 수가 1 인 pair = (2, 3) 유일
- 이 수가 ≥ 2 인 pair = 기타 전부

---

## Lean formalization 목표

```lean
-- E213/PairForcing.lean (미작성)

theorem pair_forcing :
    ∀ p q : ℕ, 2 ≤ p → p < q → Nat.gcd p q = 1 →
    ((∃! n, Atomic p q n) ↔ (p = 2 ∧ q = 3)) := by
  sorry

theorem pair_forcing_value :
    (∃! n, Atomic 2 3 n) ∧ (∀ n, Atomic 2 3 n ↔ n = 5) := by
  sorry
```

이 정리는 PAPER §6 의 `atomic_iff_five` 를 더 강한 statement 로
승격 — single pair (2, 3) 의 **arithmetic 유일성** 까지 증명.

---

## 실험 backup

- `FND_042`: L 일반화 (A={L,...,2L-1}), L=2 만 atomic 존재 (4/4 ✓)
- `FND_043`: coprime pair 전수, (2,3) 유일 (2/2 ✓)

---

**작성:** 2026-04-19, 213 branch 머지 후.  Prop 6.5 + Atomicity
+ ArityForcing 을 하나의 arithmetic 정리로 통합.
