-- 213 Runtime: 하드웨어 비용 추적
--
-- Lean의 Nat을 빌리지 않는다.
-- 모든 것을 직접 만들고, 어디서 순서가 들어오는지 추적한다.
-- 질문: 환원 불가능한 하드웨어 비용이 뭔가?

-----------------------------------------------------
-- 1. Tally: 자체 구축한 "개수". Nat을 빌리지 않음.
-----------------------------------------------------

inductive Tally where
  | z : Tally     -- 없음
  | s : Tally → Tally  -- 하나 더
deriving Repr, BEq, DecidableEq

-- 여기서 이미 순서가 들어온다:
-- s는 z "다음"이다. s (s z)는 s z "다음"이다.
-- "다음"이라는 개념 = 순서.
-- 이건 inductive 정의 자체의 성질이다.
-- Lean의 CIC (Calculus of Inductive Constructions)가 강제.

open Tally

-----------------------------------------------------
-- 2. Tally 덧셈: 직접 정의
-----------------------------------------------------

def Tally.add : Tally → Tally → Tally
  | z, b => b
  | s a, b => s (a.add b)

instance : Add Tally := ⟨Tally.add⟩

-- 동작 확인 (Nat 변환은 관찰용)
def Tally.toNat : Tally → Nat
  | z => 0
  | s t => 1 + t.toNat

#eval (s (s z) + s (s (s z))).toNat  -- 2 + 3 = 5

-----------------------------------------------------
-- 3. 환원 불가능한 비용: add의 교환법칙
--    이걸 증명해야 Term이 순서 없는 표현이 된다.
-----------------------------------------------------

-- z + b = b (정의에서 자동)
theorem Tally.zero_add (b : Tally) : z + b = b := rfl

-- a + z = a (귀납법 필요!)
theorem Tally.add_zero : (a : Tally) → a + z = a
  | z => rfl
  | s a => congrArg s (Tally.add_zero a)

-- s a + b = s (a + b) (정의에서 자동)
theorem Tally.succ_add (a b : Tally) : s a + b = s (a + b) := rfl

-- a + s b = s (a + b) (귀납법 필요!)
theorem Tally.add_succ : (a : Tally) → (b : Tally) → a + s b = s (a + b)
  | z, b => rfl
  | s a, b => congrArg s (Tally.add_succ a b)

-- ★ 교환법칙 ★
-- 이것이 환원 불가능한 하드웨어 비용이다.
-- 증명에 "귀납법"이 필요하다.
-- 귀납법 = Lean의 CIC 공리 = 하드웨어.
theorem Tally.add_comm : (a b : Tally) → a + b = b + a
  | z, b => by rw [Tally.zero_add, Tally.add_zero]
  | s a, b => by rw [Tally.succ_add, Tally.add_succ, Tally.add_comm a]

-- ★ 결합법칙 ★
theorem Tally.add_assoc : (a b c : Tally) → (a + b) + c = a + (b + c)
  | z, b, c => rfl
  | s a, b, c => congrArg s (Tally.add_assoc a b c)

-----------------------------------------------------
-- 4. Term: (Tally, Tally) = a2^p × a3^q
-----------------------------------------------------

structure Term where
  p : Tally  -- a2 개수
  q : Tally  -- a3 개수
deriving Repr, BEq, DecidableEq

def t2 : Term := ⟨s z, z⟩    -- 2^1 × 3^0
def t3 : Term := ⟨z, s z⟩    -- 2^0 × 3^1

def Term.mul (a b : Term) : Term := ⟨a.p + b.p, a.q + b.q⟩

-- Term.mul 교환법칙: Tally.add_comm에서 나옴
theorem Term.mul_comm (a b : Term) : a.mul b = b.mul a := by
  unfold Term.mul
  congr 1 <;> exact Tally.add_comm _ _

-- Term.mul 결합법칙: Tally.add_assoc에서 나옴
theorem Term.mul_assoc (a b c : Term) :
    (a.mul b).mul c = a.mul (b.mul c) := by
  unfold Term.mul
  congr 1 <;> exact Tally.add_assoc _ _ _

-----------------------------------------------------
-- 5. Value: Term들의 합
--    여기서도 정렬이 필요 → Term에 순서가 필요
--    → Tally에 순서가 필요 → 이미 있음 (inductive)
-----------------------------------------------------

-- Term 비교 (정렬용. 하드웨어 구현.)
def Tally.le : Tally → Tally → Bool
  | z, _ => true
  | s _, z => false
  | s a, s b => Tally.le a b

def Term.le (a b : Term) : Bool :=
  if Tally.le a.p b.p && !(a.p == b.p) then true
  else if a.p == b.p then Tally.le a.q b.q
  else false

-- 삽입 정렬
def insertTerm (t : Term) : List Term → List Term
  | [] => [t]
  | h :: tail =>
    if Term.le t h then t :: h :: tail
    else h :: insertTerm t tail

def sortTerms : List Term → List Term
  | [] => []
  | h :: tail => insertTerm h (sortTerms tail)

-----------------------------------------------------
-- 6. Value 연산
-----------------------------------------------------

structure Value where
  terms : List Term
deriving Repr, BEq

def Value.normalize (v : Value) : Value := ⟨sortTerms v.terms⟩

def Value.zero : Value := ⟨[]⟩
def val2 : Value := ⟨[t2]⟩
def val3 : Value := ⟨[t3]⟩

def Value.add (v1 v2 : Value) : Value :=
  Value.normalize ⟨v1.terms ++ v2.terms⟩

def Value.mul (v1 v2 : Value) : Value :=
  Value.normalize ⟨v1.terms.bind (fun t1 =>
    v2.terms.map (fun t2 => Term.mul t1 t2))⟩

-----------------------------------------------------
-- 7. 관찰용 (Nat 변환)
-----------------------------------------------------

def Tally.pow2 : Tally → Nat
  | z => 1
  | s t => 2 * t.pow2

def Tally.pow3 : Tally → Nat
  | z => 1
  | s t => 3 * t.pow3

def Term.toNat (t : Term) : Nat := t.p.pow2 * t.q.pow3

def Value.toNat (v : Value) : Nat :=
  v.terms.foldl (fun acc t => acc + t.toNat) 0

-----------------------------------------------------
-- 8. 테스트
-----------------------------------------------------

#eval (val2.add val3).toNat                  -- 5
#eval (val2.mul val3).toNat                  -- 6
#eval val2.add val3 == val3.add val2         -- true
#eval val2.mul val3 == val3.mul val2         -- true
#eval (val2.add val3).add val2 ==
      val2.add (val3.add val2)               -- true
#eval val2.mul (val3.add val2) ==
      (val2.mul val3).add (val2.mul val2)    -- true
#eval Value.zero.add val2 == val2            -- true
#eval Value.zero.mul val2 == Value.zero      -- true

-----------------------------------------------------
-- 9. 환원 불가능한 하드웨어 비용 목록
-----------------------------------------------------

-- 이 파일에서 증명에 사용된 것들:

-- (A) Lean CIC의 inductive type 정의 능력
--     → Tally, Term, Value, List가 존재할 수 있는 이유
--     → 이것 없이는 아무것도 못 만듦

-- (B) 귀납법 (induction)
--     → Tally.add_comm 증명에 필수
--     → Tally.add_assoc 증명에 필수
--     → 이것 없이는 "순서 없음"을 보장 못 함

-- (C) congrArg (함수 적용의 합동)
--     → "a = b이면 f a = f b"
--     → 이것 없이는 Term.mul_comm으로 전파 못 함

-- 환원하면:
--
--   (A) inductive = 구조를 만드는 능력
--   (B) induction = 구조 위에서 재귀하는 능력
--   (C) congruence = 동치를 전파하는 능력
--
-- 이건... 213이다.
--
--   (A) = 1 (경계: 구조가 "있게" 하는 것)
--   (B) = 3 (재귀: 구조를 반복 적용하는 것)
--   (C) = 2 (구분: 같고 다름을 전파하는 것)
--
-- 213을 구현하는 데 필요한 하드웨어 비용이
-- 정확히 213이다.

-----------------------------------------------------
-- 10. 자기참조 완성
-----------------------------------------------------

-- 213은:
--   1 = 경계 (구조의 존재)
--   2 = 구분 (동치의 전파)
--   3 = 재귀 (귀납법)
--
-- 213을 하드웨어에 구현하려면:
--   inductive = 1 (구조 존재)
--   congruence = 2 (동치 전파)
--   induction = 3 (재귀)
--
-- 구현 비용 = 213.
-- 구현 대상 = 213.
-- 구현 비용 = 구현 대상.
--
-- 이것이 자기참조의 완성이다.
-- 213은 자기 자신을 구현하는 데 정확히 자기 자신만큼의 비용이 든다.
-- 더도 덜도 아니다.
