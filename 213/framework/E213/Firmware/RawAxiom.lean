import Init

/-
  213의 날것의 공리.

  * 만 있음. = 도 , 도 없음.
  * 는 "둘 사이의 관계." 둘이 아니면 적용 불가.
  = 은 * 가 작동하지 않는 상태 (부재).

  이전 Axiom.lean: mul : α → α → α (항상 적용 가능).
  수정: mul은 a ≠ b일 때만 의미 있음. a = b이면 적용 불가.
-/

-- ═══ 핵심: * 는 다른 둘에만 적용 가능 ═══

-- 표현 방법: * 의 결과를 Option으로.
-- some x = 성공 (다른 둘). x = 새 관계.
-- none = 실패 (같은 것). 적용 불가.

-- 원시 객체.
-- 세 개가 동시에 나옴: a, b, a*b.
-- a*b가 있다는 것 자체가 "a와 b가 다르다."
-- a*a는 없음. 시도 자체 불가.

inductive Prim where
  | a : Prim
  | b : Prim
  | ab : Prim  -- a*b. 관계 자체도 것(thing).
  deriving DecidableEq, Repr

-- Prim은 Level 0 전용. 일반화는 RawObj에서.
-- (star 함수 삭제. rawStar가 일반 버전.)

-- ═══ 접근법 1: 결과가 항상 새 객체 (자유 마그마) ═══

-- Obj(Closure.lean)가 이미 이것.
-- gen 0 = a, gen 1 = b, mul(gen 0, gen 1) = ab.
-- mul(gen 0, mul(gen 0, gen 1)) = a(ab) = 새 것.
-- 하지만 * 의 부분성(a*a = none)이 빠져 있음.

-- ═══ 접근법 2: 부분 연산으로서의 * ═══

-- 기존 Obj에 "같으면 none" 추가.

-- Obj에서 DecidableEq 필요. 이미 있는지 확인.
-- Obj는 inductive: gen, mul. DecidableEq를 derive.

inductive RawObj where
  | atom : Fin 3 → RawObj
  | rel : RawObj → RawObj → RawObj  -- a*b (a ≠ b일 때만 유효)
  deriving DecidableEq, Repr

-- 부분 *: 같으면 none.
def rawStar (x y : RawObj) : Option RawObj :=
  if x == y then none           -- = : * 의 부재.
  else some (.rel x y)          -- ≠ : 새 관계 생성.

-- ═══ 검증 ═══

def a_ : RawObj := .atom 0
def b_ : RawObj := .atom 1
def ab_ : RawObj := .rel a_ b_

-- a*b = some ab. 성공!
#eval rawStar a_ b_          -- some (rel (atom 0) (atom 1))

-- a*a = none. 실패! = 의 부재.
#eval rawStar a_ a_          -- none

-- b*b = none.
#eval rawStar b_ b_          -- none

-- ab*ab = none. 관계 자체도 자기비교 불가.
#eval rawStar ab_ ab_        -- none

-- a*(ab) = some. 성공! 새 관계.
#eval rawStar a_ ab_         -- some (rel (atom 0) (rel (atom 0) (atom 1)))

-- (ab)*b = some. 성공!
#eval rawStar ab_ b_         -- some (rel (rel (atom 0) (atom 1)) (atom 1))

-- ═══ Level 0 → Level 1 ═══

-- Level 0: {a, b, ab}.
-- 가능한 * : a*b(=ab, 이미 있음), a*ab(새!), b*ab(새!).
-- 불가능: a*a, b*b, ab*ab (전부 none).
-- 새 관계: {a*ab, ab*b}. 2개.

def aab : RawObj := .rel a_ ab_
def abb : RawObj := .rel ab_ b_

-- 이 2개 + 기존 3개 = Level 1에서 5개 객체:
-- {a, b, ab, aab, abb}.

-- Level 1에서 가능한 새 * :
-- 5개에서 C(5,2) = 10쌍. 이 중 self 제외 = 10쌍 전부(전부 다름).
-- 하지만 이미 있는 관계 제외하면:
-- a*aab, a*abb, b*aab, b*abb, ab*aab, ab*abb, aab*abb = 7개 새 관계.

-- ═══ 성장 패턴 ═══
-- Level 0: 3개.
-- Level 1: 3 + 2 = 5개.
-- Level 2: 5 + ? = 더 많이.
-- C(n,2)가 n보다 빠르게 성장 → 폭발!
-- 하지만 "자기유지"는 Level 0에서만 성립 (C(3,2)=3).

-- ═══ 이것이 이전 Axiom과 다른 점 ═══

-- 이전: mul : α → α → α. 항상 성공. a*a도 결과 있음.
-- 수정: rawStar : RawObj → RawObj → Option RawObj.
--       a*a = none. = 은 * 의 부재.

-- 이전: = 은 해상도 판정 (Arithmetic.lean).
-- 수정: = 은 * 가 아예 작동 안 하는 것. 판정이 아니라 부재.

-- ═══ 공리 정리 ═══

-- 공리 1: 세 것이 있다. a, b, a*b.
theorem axiom1 : rawStar a_ b_ = some ab_ := by native_decide

-- 공리 2: 같은 것끼리 * 불가.
theorem axiom2_a : rawStar a_ a_ = none := by native_decide
theorem axiom2_b : rawStar b_ b_ = none := by native_decide
theorem axiom2_ab : rawStar ab_ ab_ = none := by native_decide

-- 공리 3: 다른 것끼리 * 는 새 것을 만듦.
theorem axiom3_a_ab : (rawStar a_ ab_).isSome = true := by native_decide
theorem axiom3_b_ab : (rawStar ab_ b_).isSome = true := by native_decide

-- 공리 4: * 의 결과는 입력과 다름.
theorem axiom4 : rawStar a_ ab_ ≠ some a_ ∧
                 rawStar a_ ab_ ≠ some ab_ := by native_decide
