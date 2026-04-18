import E213.Meta.TheoremDB

/-
  213 정리 번역의 패턴 과 노하우.

  75개 정리 구축 경험에서 도출.
  각 패턴: 반복 발견되는 증명 구조.
  각 노하우: 효율적 증명 기법.
-/

-- ═══ 패턴 1: Decide 지배 ═══

-- 관찰: 유한 domain 문제의 대부분이 `decide` 로 해결.
-- 예: Fin 3 공리, Bool 논리, Z/nZ 군.

-- 조건: decidable proposition + 유한 search space.
-- Lean 이 decidability instance 자동 생성 (Fin, Bool, DecidableEq).

-- 노하우:
--   먼저 `by decide` 시도.
--   실패 시 `by revert; decide` (universal case).
--   실패 시 induction / interval_cases.

-- ═══ 패턴 2: 기존 정리 재사용 ═══

-- 관찰: 대부분 정리가 이미 증명된 framework 결과의 alias.
-- 예: thm_005 = atom_is_not_made.
-- 예: thm_013 = Nat213.zero_ne_succ.

-- 노하우:
--   새 정리 추가 전 framework 검색.
--   이미 있으면 alias 만. 없으면 새 증명.
--   통일된 naming 으로 ID 체계 유지.

-- ═══ 패턴 3: 계층별 의존성 ═══

-- Firmware (Raw, /) ← 공리.
-- Hypervisor (Lens) ← Raw 위 fold.
-- OS (Peano, Logic, Set, ...) ← Lens 선택.
-- Meta (Provability, Classifier) ← OS 위 reflection.
-- Applications ← Meta 활용.

-- 노하우:
--   위 계층은 아래만 참조.
--   순환 import 피하기.
--   Firmware 수정 시 전체 영향 고려.

-- ═══ 패턴 4: Fold = Catamorphism ═══

-- 관찰: 모든 "수" 는 Raw.fold 의 특수화.
-- 렌즈 (g, h) 고르면 자동 수 생성.

-- 노하우:
--   새 수 만들 때 `Lens α := ⟨g, h⟩` 형태.
--   h commutative → 좌우 대칭 수.
--   h 비대칭 → 방향성 있는 수.

-- ═══ 패턴 5: Kernel = Equivalence ═══

-- 관찰: 모든 "같다" 는 어떤 렌즈의 kernel.
-- L.equiv x y := L.view x = L.view y.
-- Refl/symm/trans 자동 (함수 kernel 일반).

-- 노하우:
--   공리계 "= 정의" 때 렌즈 먼저 고름.
--   kernel 이 자동 equivalence.
--   Setoid 인스턴스 바로.

-- ═══ 패턴 6: Rule 계단 ═══

-- 관찰: 6 Rule (R1-R6) 중 하나 제거 → level 하강.
-- R3 (recursion) 가 유일 "무한 생산 규칙."
-- 다른 rule 은 구조 조정.

-- 노하우:
--   새 공리계 분석 시 R1-R6 profile.
--   각 rule 제거로 difficulty 정량.
--   Cayley-Dickson 평행 (7 성질).

-- ═══ 패턴 7: Stream = 경계 ═══

-- 관찰: Raw 는 countable. Stream = Raw boundary at ∞ = 연속체.
-- Finite Raw + Stream = ℝ, ℂ level.

-- 노하우:
--   유한 객체 = inductive Raw.
--   무한 객체 = Nat → Bool (RealPath).
--   실제 실수 = Stream 해석 (렌즈 의존).

-- ═══ 노하우 요약 (증명 순서) ═══

-- 1. `by decide` 시도 (유한).
-- 2. `by simp [...]` 시도 (정의 전개).
-- 3. `by induction x with ...` (재귀).
-- 4. Framework 내 alias 로 해결.
-- 5. 새 증명 (rare).

-- ═══ 노하우 요약 (DB 관리) ═══

-- 1. thm ID 순차. Namespace 로 묶지 않음.
-- 2. TheoremEntry metadata (difficulty, category, verdict).
-- 3. path: 어느 module 에서 증명.
-- 4. DB 는 append-only list.
-- 5. 새 version v_{n+1} := v_n ++ [...]
-- 6. 검증은 `by decide` 로.

-- ═══ 관찰된 통계 ═══

-- 75 정리 중:
--   Provable: 74 (98.7%).
--   Unknown: 1 (RH).
-- Difficulty 분포:
--   0-3: 9 (Firmware, 12%).
--   4-7: 28 (Hypervisor + OS, 37%).
--   8-10: 33 (Meta + Apps, 44%).
--   11-14: 5 (Stream, 7%).
-- Category:
--   decided: 73.
--   kernelFail: 1 (RH).
--   selfReference: 1 (Gödel).
