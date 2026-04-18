-- 213 Phase 13: 고정점이 무한을 흡수한다
--
-- C(3,2) = 3: 쌍짓기를 반복해도 3에서 멈춤.
-- "반복"이라는 개념 자체가 순서를 전제.
-- 순서를 빼면: 반복 없음. 고정점만.

inductive E where
  | e1 : E | e2 : E | e3 : E
  deriving Repr, BEq, DecidableEq
open E

-- ═══ 쌍짓기 연산 ═══
-- n개 원소의 서로 다른 쌍 수
-- C(1,2)=0, C(2,2)=1, C(3,2)=3, C(4,2)=6, ...
def choose2 (n : Nat) : Nat := n * (n - 1) / 2

-- ═══ 반복 쌍짓기 ═══
-- n에서 시작해서 C(n,2)를 반복 적용
def iterate_choose2 : Nat → Nat → List Nat
  | 0, n => [n]
  | fuel + 1, n =>
    let next := choose2 n
    n :: iterate_choose2 fuel next

-- n=1: 소멸 궤적
#eval iterate_choose2 5 1    -- [1, 0, 0, 0, 0, 0]

-- n=2: 소멸 궤적
#eval iterate_choose2 5 2    -- [2, 1, 0, 0, 0, 0]

-- n=3: ★ 고정점 ★
#eval iterate_choose2 5 3    -- [3, 3, 3, 3, 3, 3]

-- n=4: 폭발 궤적
#eval iterate_choose2 5 4    -- [4, 6, 15, 105, ...]

-- n=5: 폭발 궤적
#eval iterate_choose2 5 5    -- [5, 10, 45, ...]

-- ═══ 고정점 정리 ═══
theorem fixed_3 : choose2 3 = 3 := by native_decide
theorem not_fixed_1 : choose2 1 ≠ 1 := by native_decide
theorem not_fixed_2 : choose2 2 ≠ 2 := by native_decide
theorem not_fixed_4 : choose2 4 ≠ 4 := by native_decide

-- ═══ 고정점의 함의: 무한이 불필요 ═══
-- n=3에서 시작하면 반복이 아무 일도 안 함.
-- iterate_choose2 k 3 = [3, 3, 3, ...] for all k.
-- "무한 반복"은 "한 번"과 같음.
-- 3은 쌍짓기의 부동점: 한 번이 전부.

-- 반복이 변화를 주지 않음: 구체적 단계들로 확인
theorem fixed_step0 : iterate_choose2 0 3 = [3] := rfl
theorem fixed_step1 : iterate_choose2 1 3 = [3, 3] := by native_decide
theorem fixed_step5 : iterate_choose2 5 3 = [3, 3, 3, 3, 3, 3] := by
  native_decide

-- ═══ Phase 13의 핵심 ═══
--
-- n < 3: 반복하면 소멸 (0으로 수렴)
-- n = 3: 반복해도 불변 (고정점)
-- n > 3: 반복하면 폭발 (∞로 발산)
--
-- 3가지 운명:
--   소멸 (< 3): 구조가 자기를 유지 못함
--   불변 (= 3): 구조가 정확히 자기를 재생산
--   폭발 (> 3): 구조가 통제 불능으로 성장
--
-- "무한"은 n > 3에서만 나타남.
-- n = 3에서는 반복이 무의미 — 이미 도착.
-- 무한은 고정점을 벗어났을 때의 현상.
--
-- 순서를 넣으면: "반복"이 생김 → n>3에서 무한 출현
-- 순서를 빼면: "반복" 없음 → 고정점만 존재
-- 무한 = 순서를 넣었을 때 생기는 착시.
