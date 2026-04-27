# 213 Kernel — Phase 계획 상세 (KB → KH)

각 Phase = 단일 Lean 파일 (~80줄), `#print axioms` 가 모두 빈
리스트로 끝나야 통과.

## Phase KB — Comparison primitives  (`Kernel/Compare.lean`)

목표: `Term → Term → Bool` 형태의 결정 가능 비교 추가.
  - `Term.le_b` : `a ≤ b` 를 Bool 로
  - `Term.lt_b` : `<`
  - 증명: `le_b a b = true ↔ eval a ≤ eval b` (Bool 등식 형태)

검증: `#print axioms` 빈 리스트.  ← `decide`/`Classical` 미사용.

## Phase KC — Pair / G-relation  (`Kernel/Pair.lean`)

CLAUDE.md 공리 "things with pairwise relations" 직접 반영:
  - `Term` 에 `pair : Term → Term → Term` 추가
  - 의미: G_ij = 두 entity 의 distinguishing weight (Bool/Nat)
  - `eval_pair (i j) := if equiv i j then 0 else 1`

이걸로 *대각/비대각* 구분이 kernel 에 들어옴.

## Phase KD — Rational arithmetic  (`Kernel/Rat.lean`)

DRLT 는 ℕ + ℚ 만 필요 (CLAUDE.md "유한 이산 격자").
  - `Term` 에 `frac : Term → Term → Term` (분자/분모)
  - `eval_q : Term → ℚ` (Lean Rat = structure → 0 axiom)
  - cross-multiplication 으로 비교

결과: 6/10, 137/100 같은 213 비율 axiom-free.

## Phase KE — Decide procedure  (`Kernel/Decide.lean`)

Lean `decide` tactic 우회.  유한 enumeration 으로 충분:
  - `Term.holds : Term → Bool`  (predicate Term 의 truth)
  - `Term.allBelow : ℕ → (ℕ → Bool) → Bool`  (∀x<n, p x)

이거 깔리면 "n 이하의 모든 페어" 같은 명제도 axiom-free.

## Phase KF — Soundness 다리  (`Kernel/Sound.lean`)

deep ↔ shallow 다리:
  - `Sound_eq : equiv a b = true → eval a = eval b`
  - `Sound_le : le_b a b = true → eval a ≤ eval b`

증명: 구조귀납 + Nat 산술.  Lean Eq (intensional) 만 사용,
propext 없음.  `#print axioms` 빈 리스트 유지.

이 정리들이 닫히면 Bool 결과 → Prop 결과 *upgrade* 무료.

## Phase KG — 핵심 capstone 포팅  (`Kernel/Cap_*.lean`)

야심 milestone: 213 의 핵심 정수 결과를 Term encoding 으로:
  - α_GUT 의 정수 토대 (d², 6, 25)
  - magic numbers chain (2, 8, 20, 28, 50, 82, 126)
  - period closures (2 n_S², 2 n_S³, ...)

각 capstone 의 `#print axioms` 가 빈 리스트.

## Phase KH — 점진 포팅 도구  (`tools/port_to_kernel.py`)

기존 620 파일 → kernel encoding 자동 보조:
  - `decide` 호출 패턴 detect
  - Nat/Rat 산술 → Term DSL 변환 시도
  - `#print axioms` 자동 회귀 테스트

마라톤 종료 = "핵심 capstone 5개 이상 axiom-free".

---

## 5. 다른 트랙 연결

  - 모든 트랙 (math/physics) capstone 이 KG 이후 *순차* 포팅 대상
  - blueprints/math/13_meta_213.md "Library Meta" 와 직결
  - catalogs/ 와 동기화 (axiom-free 닫힘 표시 컬럼 추가)

## 6. 미해결 문제

  Q1. 어디까지 ℕ/ℚ 만으로 가능?  φ=(1+√5)/2 algebraic 수는
      minimal polynomial Term 으로 표현?
  Q2. "Lean 의 Eq 자체" 를 213 안으로 흡수 가능한가?
  Q3. 어디에서든 Iff 를 Eq 로 변환 = propext 발동.  완전 우회?
  Q4. higher-order 관계 (G_ij 의 G_ij) — 다음 단계.
