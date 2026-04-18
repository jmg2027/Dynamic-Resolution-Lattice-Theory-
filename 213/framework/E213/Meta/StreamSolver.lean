import E213.Meta.ProblemSolver

/-
  무한 차원 (Stream) 자동 Problem Solver.

  핵심 아이디어: Prefix-based Progressive Solver.
    1. Stream 명제 → 유한 prefix 조건 으로 근사.
    2. N 증가시키며 verdict 축적.
    3. 반례 발견 즉시 Refute.
    4. N = ∞ 극한은 부분 증거.

  완전 자동화 불가 (RealPath 무한).
  하지만 실용적 verdict 가능.
-/

-- ═══ StreamProblem: prefix-checkable 명제 ═══

structure StreamProblem where
  name : String
  -- 첫 n 비트 만으로 판정 가능한 predicate.
  prefixCheck : RealPath → Nat → Bool

-- Progressive verdict: N bit 까지 확인.
def StreamProblem.verdictAt (P : StreamProblem) (r : RealPath)
    (N : Nat) : Bool := P.prefixCheck r N

-- ═══ 예시 1: "처음 N 비트가 모두 zero" ═══

def prob_zero_prefix : StreamProblem :=
  { name := "First N bits all zero"
    prefixCheck := fun r n =>
      (List.range n).all (fun i => !(r i)) }

-- RealPath.zero 는 모든 N 에서 true.
example : prob_zero_prefix.verdictAt RealPath.zero 10 = true :=
  by native_decide

-- RealPath.ones 는 N=1 부터 false.
example : prob_zero_prefix.verdictAt RealPath.ones 1 = false :=
  by native_decide

-- RealPath.half (0.1000...) 는 N=1 에서 false, N=0 에서 true.
example : prob_zero_prefix.verdictAt RealPath.half 0 = true :=
  by native_decide
example : prob_zero_prefix.verdictAt RealPath.half 1 = false :=
  by native_decide

-- ═══ 예시 2: "주기성 검출 (period 2)" ═══

def prob_period_2 : StreamProblem :=
  { name := "First N bits alternate"
    prefixCheck := fun r n =>
      (List.range n).all (fun i => r i = !(r (i + 1))) }

-- Alternating stream.
def r_alt : RealPath := fun n => n % 2 = 0

example : prob_period_2.verdictAt r_alt 5 = true := by native_decide
example : prob_period_2.verdictAt RealPath.zero 2 = false :=
  by native_decide

-- ═══ Progressive verdict batch ═══

-- 여러 N 에서 verdict (극한 수렴 추적).
def StreamProblem.progressionTable (P : StreamProblem) (r : RealPath)
    (maxN : Nat) : List (Nat × Bool) :=
  (List.range (maxN + 1)).map (fun n => (n, P.verdictAt r n))

-- 예시: r_alt 의 period_2 점진.
example : (prob_period_2.progressionTable r_alt 3).length = 4 :=
  by native_decide

-- ═══ Counterexample finder ═══

-- 첫 false 위치 (있으면).
def StreamProblem.firstFalseIdx (P : StreamProblem) (r : RealPath)
    (maxN : Nat) : Option Nat :=
  (List.range (maxN + 1)).find? (fun n => !(P.verdictAt r n))

-- RealPath.ones 에서 zero_prefix false 는 n=1 부터.
example : prob_zero_prefix.firstFalseIdx RealPath.ones 10 = some 1 :=
  by native_decide
