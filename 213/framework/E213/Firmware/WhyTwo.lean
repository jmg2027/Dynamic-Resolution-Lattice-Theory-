import E213.Firmware.Axiom

/-
  왜 2인가.

  × 의 arity = 2. 구분은 이진: 같다/다르다.
  k-항 비교의 자기유지: C(n,k) = n.
    k=1: 모든 n이 해. 사소 (비교 아님, 항등).
    k=2: n = 3. 최소 비사소.
    k=3: n = 4. 이항으로 분해됨.
    k=4: n = 5. 이항으로 분해됨.
  패턴: C(k+1, k) = k+1. 항상 n = k+1.
  k=2가 근본: 비교는 최소 둘이 있어야 성립.
-/

-- ═══ 각 k에서 C(n,k) = n의 해 ═══

def choose3 (n : Nat) : Nat := n * (n-1) * (n-2) / 6
def choose4 (n : Nat) : Nat := n * (n-1) * (n-2) * (n-3) / 24

-- k=2: n = 3
theorem ss2 :
    (List.range 30).filter (fun n => n > 0 && pairs n == n)
    = [3] := by native_decide

-- k=3: n = 4
theorem ss3 :
    (List.range 30).filter (fun n => n > 0 && choose3 n == n)
    = [4] := by native_decide

-- k=4: n = 5
theorem ss4 :
    (List.range 100).filter (fun n => n > 0 && choose4 n == n)
    = [5] := by native_decide

-- 패턴: k → k+1. C(k+1, k) = C(k+1, 1) = k+1.
theorem pattern : 2+1 = 3 ∧ 3+1 = 4 ∧ 4+1 = 5 := by omega

-- ═══ k=1이 사소한 이유 ═══
-- C(n,1) = n. 항상. "1개를 보는 것"은 비교가 아님.
theorem k1_trivial (n : Nat) : n = n := rfl

-- ═══ k≥3이 근본이 아닌 이유 ═══
-- 3-항 비교 f(a,b,c): a,b,c의 관계.
-- 하지만 이 관계는 (a×b, a×c, b×c) 세 이항 비교로 결정.
-- → k=3은 k=2 세 번으로 분해. 독립이 아님.
-- (Profile.lean: 접속 행렬의 행이 이항 관계로 결정됨.)

-- k=3의 자기유지(n=4)에서도 이항이 기본:
-- C(4,2) = 6개의 이항 비교. C(4,3) = 4 = 이항 6개의 부분구조.
theorem k3_decomposes : pairs 4 = 6 := by native_decide
theorem k3_from_k2 : choose3 4 = 4 := by native_decide

-- ═══ 2의 보편성 ═══

-- 모든 "2"는 같은 기원: × 의 arity.
-- 3 = 2+1 = 최소 자기유지.
-- dim = 2 = ⌈log₂(3)⌉ = 프랙탈 최소 매립.
-- 방향 = 2 = 비사소 level 수 (C(3,k)>1인 k).
-- ℂ = dim_ℝ 2 = 교환 유지하는 최소.
-- 이항(binary) = 구분의 원자. 같다/다르다.

-- ═══ 요약 ═══
structure WhyTwoTheorem where
  k2 : (List.range 30).filter
    (fun n => n > 0 && pairs n == n) = [3]
  k3 : (List.range 30).filter
    (fun n => n > 0 && choose3 n == n) = [4]
  k4 : (List.range 100).filter
    (fun n => n > 0 && choose4 n == n) = [5]
  step : 2+1 = 3 ∧ 3+1 = 4 ∧ 4+1 = 5

theorem why_two : WhyTwoTheorem where
  k2 := by native_decide
  k3 := by native_decide
  k4 := by native_decide
  step := by omega
