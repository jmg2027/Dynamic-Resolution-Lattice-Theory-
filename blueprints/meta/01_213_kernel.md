# 213 Kernel — Blueprint (극단적 Purity)

**우선순위**: ★★★★ 최우선 (이론 전체의 floor 재정의)
**상태**: Phase KA 완료, KB→KH 마라톤 대기

---

## 1. 왜 이 분야인가

지금까지의 "0 외부 axiom" 은 *Lean kernel-relative*:
  - propext, Quot.sound, Classical.choice 는 *주어진 것* 으로 가정
  - DRLT 의 "things with pairwise relations" 한 줄 뒤에 *Lean CIC 가 또 있다*
  - 즉 Lean 이 213 보다 더 fundamental.  비전 위배.

**비전:** Raw/Lens 가 *진짜 floor*, Lean 은 *syntactic host*.
유한 이산 격자라서 `propext`, `Quot.sound` 같은 무한-type-theory
axiom 이 *애초에 필요 없음* (CLAUDE.md "÷, ∫, π 불필요" 동일 정신).

**달성 목표:** Lean kernel axiom *어느 것도* 213 정리의 진리값에
load-bearing 이 아니도록 — `#print axioms` 가 *literally* 빈 리스트.

비유: Lean 으로 "C++ 처럼 진짜 프로그램" 을 만드는 게 부담스러우니
Lean 을 빌려서 213 의 deep embedding 을 host.  Lean 은 type-checker
역할만 하고, 의미는 213 내부 함수가 다 결정.

## 2. 213-native 등장 — deep embedding 경로

### 2.1 데이터 = Term

```
inductive Term : Type
  | zero | succ | add | mul | (...추후 확장)
```

순수 inductive — propext 도 quotient 도 안 씀.

### 2.2 의미 = 총함수

```
def eval : Term → ℕ      -- 구조귀납, 총
def equiv : Term → Term → Bool   -- Prop 우회
```

Bool 등호 + Nat.beq → propositional extensionality 불필요.

### 2.3 정리 = rfl

`theorem T : equiv lhs rhs = true := rfl`
→ Lean 이 reduction 만 수행, 어떤 axiom 도 인용 안 함.

### 2.4 Soundness 다리 (선택)

`theorem Sound : equiv a b = true → eval a = eval b`
→ 한 번 증명하면 Bool 결과를 Prop 결과로 승격.  Lean 의 Eq 만
사용 (intensional, 0 axiom).

## 3. 이미 깔린 빌딩 블록 (Phase KA 완료)

  ✅ `lean/E213/Kernel/Term.lean`
     - `Term` inductive (zero, succ, add, mul)
     - `eval : Term → ℕ`
     - `equiv : Term → Term → Bool`
     - 표준 상수: nS=3, nT=2, d=5, c=2

  ✅ `lean/E213/Kernel/Demo.lean` — 7 capstone, 모두 0 axiom:
     - `dim_law`     n_S + n_T ≡ d
     - `c_eq_nT`     c ≡ n_T
     - `d_sq_25`     d² ≡ 5·4 + 5
     - `eval_d_sq`   eval(d·d) = 25
     - `nSnT_sq_36`  ((n_S·n_T))² = 36
     - `two_nS_sq`   2·n_S² = 18  (Argon)
     - `two_nS_cube` 2·n_S³ = 54  (Xe)

  ✅ `lake build E213.Kernel.Demo` clean
  ✅ `#print axioms` 출력 7/7 모두 "does not depend on any axioms"

## 4. Phase 계획 (KB → KH 마라톤)

각 Phase = 단일 Lean 파일 (~80줄), `#print axioms` 가 모두 빈
리스트로 끝나야 통과.
