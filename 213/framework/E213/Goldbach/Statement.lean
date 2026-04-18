import E213.Axiom
import E213.EpsilonDelta

/-
  골드바흐 추측의 213 번역.
  원본: 모든 짝수 n > 2는 두 소수의 합.
  213: ∀n, (=_1에서 0과 같고 n>2) → ∃p q, 소수(p) ∧ 소수(q) ∧ p+q=n.
-/

-- ═══ 짝수 = =_1에서 0과 같다 ═══
-- eqAt 1 n 0 = (n % 2 == 0). 해상도 1에서 0과 구분 불가.
def isEven (n : Nat) : Bool := eqAt 1 n 0

#eval isEven 4   -- true
#eval isEven 7   -- false

-- ═══ 소수 = ×의 역이 자명 ═══
-- p가 소수 ↔ p = a × b이면 a=1 또는 b=1.
-- 213: mul의 역분해가 trivial(gen 하나 + 자신).
def isPrime (n : Nat) : Bool :=
  n ≥ 2 && (List.range (n-2)).all fun d => n % (d+2) != 0

#eval isPrime 2   -- true
#eval isPrime 4   -- false
#eval isPrime 17  -- true

-- ═══ 골드바흐 조건: n = p + q ═══
-- 213: gen 두 번(p, q 선택) + 합성(+) + 소수판정(mul 역).
def goldbach (n : Nat) : Bool :=
  (List.range n).any fun p =>
    isPrime p && isPrime (n - p)

-- ═══ 추측 (유한 범위) ═══
def goldbachUpTo (bound : Nat) : Bool :=
  (List.range bound).all fun n =>
    !(isEven n && n > 2) || goldbach n

-- ═══ 골드바흐 분해쌍 찾기 ═══
def goldbachPair (n : Nat) : Option (Nat × Nat) :=
  (List.range n).findSome? fun p =>
    if isPrime p && isPrime (n - p) then some (p, n - p) else none

#eval goldbachPair 4    -- (2, 2)
#eval goldbachPair 20   -- (3, 17)
#eval goldbachPair 100  -- (3, 97)
