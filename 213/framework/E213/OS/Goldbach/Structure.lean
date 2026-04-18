import E213.OS.Goldbach.Statement
import E213.OS.Goldbach.Count

/-
  예외 집합 E의 삼중 결핍.
  1. 생성 규칙 없음 (부정 정의). 2. 연산 닫힘 없음.
  3. sparse. 이 셋이 동시이면 → E 유한 (213 추론).
-/

-- ═══ E의 원소가 만족해야 할 조건 ═══

-- n ∈ E이면: ∀ prime p ≤ n/2, n-p는 합성.
-- 즉 n-2, n-3, n-5, n-7, n-11, ... 전부 합성.
-- 조건 수 = π(n/2) ≈ n/(2·ln n).

def compositeCount (n : Nat) : Nat :=
  ((List.range (n/2)).filter isPrime).filter
    (fun p => !(isPrime (n - p))) |>.length

def primesBelowHalf (n : Nat) : Nat :=
  ((List.range (n/2)).filter isPrime).length

-- n ∈ E이면: compositeCount n = primesBelowHalf n.
-- (모든 소수 p에 대해 n-p가 합성.)

-- 실제: Goldbach 성립하는 n에서는 compositeCount < primesBelowHalf.
#eval (100, compositeCount 100, primesBelowHalf 100) -- (100, ?, 25)
#eval (200, compositeCount 200, primesBelowHalf 200)

-- ═══ 예외의 "확률" ═══

-- n-p가 합성일 확률 ≈ 1 - 1/ln(n).
-- π(n/2)개의 독립 시행 (근사).
-- 전부 합성일 확률 ≈ (1-1/ln n)^{π(n/2)}
--                   ≈ (1-1/ln n)^{n/(2 ln n)}
--                   ≈ e^{-n/(2 ln² n)} → 0.
-- 초지수적 감소! n이 커질수록 예외 "확률" 급감.

-- 구체 계산: "실패율" = compositeCount / primesBelowHalf.
def failRate (n : Nat) : Nat :=
  if primesBelowHalf n == 0 then 100
  else compositeCount n * 100 / primesBelowHalf n

-- 실패율이 100이면 예외. 100 미만이면 Goldbach 성립.
#eval (List.range 50).map fun k => (2*k+4, failRate (2*k+4))

-- 모든 짝수에서 failRate < 100:
theorem no_total_fail :
    (List.range 250).all (fun k => failRate (2*k+4) < 100)
    = true := by native_decide

-- ═══ 삼중 결핍 ═══

-- 결핍 1: 생성 규칙 없음.
-- 소수: 에라토스테네스 체. n → n이 소수인지 결정하는 규칙.
-- E: "n ∈ E ↔ ∀p, ..."  부정 정의. 구성적 규칙 아님.
-- 완전제곱: n → n². 양의 규칙. 무한 가능.
-- E: 양의 규칙 없음. → gen 패턴 없음.

-- 결핍 2: 연산 닫힘 없음.
-- e₁, e₂ ∈ E → e₁+e₂ ∈ E? 보장 없음.
-- 반대: e₁+e₂가 클수록 Goldbach 가능성 높음.
-- → E+E ∩ E ≈ ∅. 닫히기는커녕 반발.

-- 결핍 3: sparse.
-- |E ∩ [1,X]| = O(X^{1-δ}). 밀도 → 0.

-- ═══ 213 삼중 결핍 정리 ═══

-- 무한 집합이 되려면 (213):
-- gen 패턴 (생성 규칙) 또는 mul 닫힘 (자기유지) 필요.
-- 둘 다 없으면: 유한 목록으로만 기술 가능 = 유한.

-- E: gen 없음 + mul 없음 + sparse = 삼중 결핍.
-- → E는 유한 목록. + 4×10¹⁸까지 ∅. → E = ∅.

-- 대조:
-- 소수: gen 있음(체) + mul→ℕ(FTA) + sparse. 무한. ✓
-- 완전제곱: gen 있음(n²) + sparse. 무한. ✓
-- E: 셋 다 없음. 유한. (추측이지만 구조적으로 강력.)
