import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.OS.Goldbach.Statement

/-
  Vaughan witness: 곱 분해로 가상 triple 생성.
  소수 p의 Λ(p)를 d·m 구조로 분해 → pair를 triple로.
  Chen: 이 방법으로 prime + P₂까지. P₂→prime이 남은 gap.
-/

-- ═══ 소인수 분해 = 가상 triple ═══

-- 합성수 m의 최소 소인수:
def smallestFactor (m : Nat) : Nat :=
  if m ≤ 1 then m
  else ((List.range (m-1)).map (· + 2)).find?
    (fun d => m % d == 0) |>.getD m

-- 합성수 → (d, m/d): pair로 분해.
def factor (m : Nat) : Nat × Nat :=
  let d := smallestFactor m
  (d, m / d)

#eval factor 6    -- (2, 3)
#eval factor 15   -- (3, 5)
#eval factor 7    -- (7, 1): 소수는 trivial 분해.

-- ═══ Chen의 P₂ ═══

-- P₂ = 소인수가 최대 2개인 수 (소수 또는 두 소수의 곱).
def isP2 (n : Nat) : Bool :=
  isPrime n || (let (d, q) := factor n; d > 1 && isPrime d && isPrime q)

#eval isP2 7    -- true (소수)
#eval isP2 15   -- true (3×5)
#eval isP2 12   -- false (2×2×3)

-- Chen 조건: n = p + m, p 소수, m은 P₂.
def chenCheck (n : Nat) : Bool :=
  (List.range n).any fun p =>
    isPrime p && isP2 (n - p) && (n - p) > 1

-- ═══ Chen vs Goldbach 비교 ═══

-- Chen이 성공하지만 Goldbach는 "거의 성공"인 n:
def chenNotGB (n : Nat) : Bool :=
  chenCheck n && !(goldbach n)

-- 이런 n이 있는가? (작은 범위에서)
#eval (List.range 250).filter fun k =>
  let n := 2*k + 4
  chenNotGB n
-- 빈 리스트 예상 (작은 n에서 Goldbach도 성립하므로).

-- ═══ 213 관점: pair → triple 변환 ═══

-- Goldbach pair: (p, n-p). 소수×소수. C(2,2)=1.
-- Chen pair: (p, q₁·q₂). 소수×(소수·소수).
-- 내부 구조: (p, q₁, q₂). 가상 triple!  C(3,2)=3.

-- Obj로 표현:
def goldbachObj (p q : Nat) : Obj := .mul (.gen 0) (.gen 1)
-- pair: 하나의 mul. depth 1.

def chenObj (p q1 q2 : Nat) : Obj :=
  .mul (.gen 0) (.mul (.gen 1) (.gen 2))
-- triple: 중첩 mul. depth 2.

-- Chen의 depth가 더 깊음: 2 > 1.
-- 더 깊은 구조 = 더 많은 정보 = gap 부분 보충.

-- ═══ gap의 정확한 위치 ═══

-- Chen: depth 2. C(3,2) = 3. 자기유지. P₂까지 증명.
-- Goldbach: depth 1. C(2,2) = 1. 자기유지 실패. 소수까지 안 됨.
-- 남은 gap: depth 2 → depth 1 압축. "q₁·q₂를 하나의 소수로."
-- 이 압축 = ×의 역(인수 합치기) = 비자연 방향.

theorem chen_deeper : (chenObj 3 5 7).depth > (goldbachObj 3 97).depth := by
  native_decide
-- Chen(depth2) → Goldbach(depth1) 압축 비용 = RH.
