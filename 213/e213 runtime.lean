-- 213 Runtime v2
--
-- Lean은 하드웨어. 이 코드는 213 VM을 구현한다.
-- VM 안에서는 순서가 없다.
--
-- 핵심 관찰: Atom이 2종류뿐이므로,
-- Term = (a2 개수, a3 개수)로 표현하면 순서가 사라진다.
-- 정렬이 필요 없다. 개수 세기가 정규화를 대신한다.

-----------------------------------------------------
-- 1. Term: 원자들의 곱 = (a2 개수, a3 개수)
-----------------------------------------------------

-- Term은 2^p × 3^q를 나타낸다.
-- 순서 없음이 구조에 내장됨. 교환법칙 불필요.
structure Term where
  p : Nat  -- a2(=2)의 개수
  q : Nat  -- a3(=3)의 개수
deriving Repr, BEq, DecidableEq

-- 단일 원자
def t2 : Term := ⟨1, 0⟩   -- 2
def t3 : Term := ⟨0, 1⟩   -- 3

-- Term의 곱 = 지수를 더함
def Term.mul (a b : Term) : Term := ⟨a.p + b.p, a.q + b.q⟩

-- Term의 Nat 값 (관찰용)
def Term.toNat (t : Term) : Nat := (2 ^ t.p) * (3 ^ t.q)

-- Term 정렬용 (Value 정규화에 사용)
def Term.le (a b : Term) : Bool :=
  if a.p < b.p then true
  else if a.p > b.p then false
  else a.q ≤ b.q

-----------------------------------------------------
-- 2. Value: Term들의 합 = Term의 정렬된 리스트
-----------------------------------------------------

-- 삽입 정렬 (하드웨어 구현. 213 내부 구조 아님.)
def insertSorted (t : Term) : List Term → List Term
  | [] => [t]
  | h :: tail =>
    if Term.le t h then t :: h :: tail
    else h :: insertSorted t tail

def sortTerms : List Term → List Term
  | [] => []
  | h :: tail => insertSorted h (sortTerms tail)

structure Value where
  terms : List Term  -- 정렬됨 (하드웨어가 보장)
deriving Repr, BEq

def Value.normalize (v : Value) : Value := ⟨sortTerms v.terms⟩

-----------------------------------------------------
-- 3. 213 네이티브 연산
-----------------------------------------------------

-- e₁ = 0 = 빈 Value
def Value.zero : Value := ⟨[]⟩

-- 원자 값
def val2 : Value := ⟨[t2]⟩
def val3 : Value := ⟨[t3]⟩

-- 더하기: 1을 놓는 것. Term 리스트를 합치고 정규화.
def Value.add (v1 v2 : Value) : Value :=
  Value.normalize ⟨v1.terms ++ v2.terms⟩

-- 곱하기: 1을 빼는 것. 분배법칙이 정의에 내장.
def Value.mul (v1 v2 : Value) : Value :=
  Value.normalize ⟨v1.terms.bind (fun t1 =>
    v2.terms.map (fun t2 => Term.mul t1 t2))⟩

-- Nat 변환 (관찰용)
def Value.toNat (v : Value) : Nat :=
  v.terms.foldl (fun acc t => acc + t.toNat) 0

-----------------------------------------------------
-- 4. 테스트: 공리 없이 산술이 작동하는가
-----------------------------------------------------

-- 기본 연산
#eval (val2.add val3).toNat                          -- 5
#eval (val2.mul val3).toNat                          -- 6

-- 교환: 하드웨어가 정규화로 처리
#eval val2.add val3 == val3.add val2                 -- true
#eval val2.mul val3 == val3.mul val2                 -- true

-- 결합: 하드웨어가 정규화로 처리
#eval (val2.add val3).add val2 == val2.add (val3.add val2)  -- true
#eval (val2.mul val2).mul val3 == val2.mul (val2.mul val3)  -- true

-- 분배: mul 정의에 내장
#eval val2.mul (val3.add val2) == (val2.mul val3).add (val2.mul val2)  -- true

-- e₁(0)의 성질
#eval Value.zero.add val2 == val2                    -- true (0+x = x)
#eval Value.zero.mul val2 == Value.zero              -- true (0×x = 0)

-- 2+3 = 5, 2×3 = 6, 2²×3 = 12
#eval (val2.add val3).toNat                          -- 5
#eval (val2.mul val3).toNat                          -- 6
#eval (val2.mul val2).mul val3 |>.toNat              -- 12

-- 모든 자연수 2-10
#eval val2.toNat                                                    -- 2
#eval val3.toNat                                                    -- 3
#eval (val2.mul val2).toNat                                         -- 4
#eval (val2.add val3).toNat                                         -- 5
#eval (val2.mul val3).toNat                                         -- 6
#eval ((val2.mul val2).add val3).toNat                              -- 7
#eval ((val2.mul val2).mul val2).toNat                               -- 8
#eval (val3.mul val3).toNat                                         -- 9
#eval ((val2.mul val2).add (val2.mul val3)).toNat                    -- 10

-----------------------------------------------------
-- 5. 수리비 회계
-----------------------------------------------------

-- e213_223.lean (공리 기반):
--   공리 12개 (매체 9 + 고유 3)
--   교환, 결합, 분배를 공리로 선언하고 증명
--
-- e213_runtime.lean (런타임 기반):
--   공리 0개
--   세 정의: Value.zero, Value.add, Value.mul
--   교환, 결합, 분배는 정규화에서 자동
--
-- 12개 공리가 3개 정의로 바뀌었다.
-- 공리가 아니라 정의가 일을 한다.
-- 교환/결합은 "증명할 것"이 아니라 "표현에 순서가 없으면 자동"

-----------------------------------------------------
-- 6. swap 대칭: 런타임에서는?
-----------------------------------------------------

-- a2 ↔ a3 교환
def Term.swap (t : Term) : Term := ⟨t.q, t.p⟩
def Value.swap (v : Value) : Value :=
  Value.normalize ⟨v.terms.map Term.swap⟩

-- swap 후에도 산술 구조가 보존되는지
-- (값은 달라지지만 구조적 관계는 보존)
#eval val2.swap.toNat                    -- 3 (2가 3으로)
#eval val3.swap.toNat                    -- 2 (3이 2로)

-- swap(2+3) = swap(2) + swap(3) = 3+2 = 2+3
#eval (val2.add val3).swap == (val2.swap).add (val3.swap)   -- true

-- swap(2×3) = swap(2) × swap(3) = 3×2 = 2×3
#eval (val2.mul val3).swap == (val2.swap).mul (val3.swap)   -- true

-- swap은 산술 구조를 보존한다.
-- 하지만 toNat 값은 바뀐다! 2와 3의 수치적 구별은 eval에서 온다.
-- 공리/런타임 내부에서는 교환 가능하지만,
-- 외부 관찰(toNat)에서는 구별된다.

-----------------------------------------------------
-- 7. 관찰
-----------------------------------------------------

-- 213의 전체 내용:
--   Value.zero: 경계. 내용 없음. e₁.
--   Value.add:  1을 놓는 것. 구분. Term 리스트 합침.
--   Value.mul:  1을 빼는 것. 융합. Term 쌍곱 후 합침.
--
-- 이 세 정의가 전부. 공리는 0개.
-- 교환, 결합, 분배: 순서 없는 표현의 자동 결과.
-- 경계 흡수/소멸: 빈 리스트의 자동 결과.
--
-- 213은 공리계가 아니라 연산 체계다.
-- 공리는 순서 있는 매체에서의 수리비였다.
