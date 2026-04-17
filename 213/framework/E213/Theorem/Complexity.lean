/-
  E213/Theorem/Complexity.lean — 정렬의 213 해석

  정렬 = 순서를 벗기는 것.
  비용 = 2(구분)의 적용 횟수.
  n log n = n개 원소에서 순서를 제거하는 2의 횟수.
-/
import E213.Normalize
open Expr

-- ═══ 1. n!과 log₂(n!) ═══
-- n개 원소의 순열 수 = n!
-- 이 중 정규형 = 1개
-- 구분(2) 한 번 → 가능성 ÷ 2
-- 필요한 구분 횟수 = ⌈log₂(n!)⌉

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 정수 log₂ (비트 수)
def log2_ceil (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else 1 + log2_ceil (n / 2)
termination_by n

-- 원소 수별 정렬 비용 (2의 적용 횟수)
#eval log2_ceil (factorial 1)   -- 0  (1개: 정렬 불필요)
#eval log2_ceil (factorial 2)   -- 1  (2개: 비교 1번)
#eval log2_ceil (factorial 3)   -- 3  (3개: 비교 3번)
#eval log2_ceil (factorial 4)   -- 5  (4개: 비교 5번)
#eval log2_ceil (factorial 5)   -- 7  (5개: 비교 7번)
#eval log2_ceil (factorial 10)  -- 22

-- n log₂ n 비교
def nlogn (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else n * log2_ceil n

#eval nlogn 1    -- 0
#eval nlogn 2    -- 2
#eval nlogn 3    -- 6
#eval nlogn 5    -- 15
#eval nlogn 10   -- 40

-- ═══ 2. 세 매체의 비용 ═══

-- 213 네이티브: O(1). 구조에 내장.
def cost_213 (_ : Nat) : Nat := 1

-- 순서 없는 매체 (해시/멀티셋): O(n). 한 번씩 봄.
def cost_unordered (n : Nat) : Nat := n

-- 순서 있는 매체 (리스트): O(n log n). 순서 벗기기.
def cost_ordered (n : Nat) : Nat := nlogn n

-- 비용 비교
#eval (cost_213 10, cost_unordered 10, cost_ordered 10)
-- (1, 10, 40)

#eval (cost_213 100, cost_unordered 100, cost_ordered 100)
-- (1, 100, 700)

#eval (cost_213 1000, cost_unordered 1000, cost_ordered 1000)
-- (1, 1000, 10000)

-- ═══ 3. 213 관점 ═══
-- log n = 2를 몇 번 적용하면 n이 1이 되는가.
-- = 이진 트리의 깊이.
-- = 순서의 깊이.

-- 2를 k번 적용: 2^k
-- 2^k ≥ n이 되는 최소 k = ⌈log₂ n⌉
-- 이것이 "n개를 구분하는 데 필요한 2의 횟수."

#eval log2_ceil 1     -- 0 (구분 불필요)
#eval log2_ceil 2     -- 1 (2 한 번)
#eval log2_ceil 3     -- 2 (2 두 번)
#eval log2_ceil 8     -- 3 (2 세 번)
#eval log2_ceil 1024  -- 10

-- n개 원소 각각에 대해 log n번 구분 → 총 n × log n.
-- 이것이 "순서 있는 매체에서 정규화하는 비용."

-- ═══ 4. 비용 비율 ═══
-- ordered / unordered = log n = 순서의 깊이.
-- ordered / 213 = n log n = 전체 순서 비용.
-- unordered / 213 = n = 열거 비용.

-- n = 3 (213의 고정점):
#eval cost_ordered 3   -- 6 = 2×3
#eval cost_unordered 3 -- 3
#eval cost_213 3       -- 1
-- 비율: 6 : 3 : 1.
-- 6 = 2×3 = σ₂.
-- 3 = C(3,2) = 고정점.
-- 1 = 경계.

-- n = 5 (= d):
#eval cost_ordered 5   -- 15
#eval cost_unordered 5 -- 5
#eval cost_213 5       -- 1
-- 비율: 15 : 5 : 1.
-- 15 = C(6,2). 5 = d.
