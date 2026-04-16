-- 213 (확장)
--
-- 이 코드는 타입 매체에 쓰여 있다.
-- Lean은 타입 선언을 요구한다. 이것은 매체의 제약이지 213의 성질이 아니다.

inductive E where
  | e1 : E
  | e2 : E
  | e3 : E
deriving Repr, BEq, DecidableEq

open E

-- Expr: 213의 편의 표기
inductive Expr where
  | atom : E → Expr
  | plus : Expr → Expr → Expr   -- 1이 사이에 있음
  | times : Expr → Expr → Expr  -- 1이 사이에 없음
deriving Repr

open Expr

-- eval: 1은 내용 없음 (0). 2는 2. 3은 3.
def eval : Expr → Nat
  | atom e1 => 0
  | atom e2 => 2
  | atom e3 => 3
  | plus a b => eval a + eval b
  | times a b => eval a * eval b

-----------------------------------------------------
-- 1. 기본 확인
-----------------------------------------------------

-- 213 = 2+3 = 5
#eval eval (plus (atom e2) (atom e3))  -- 5

-- 23 = 2×3 = 6
#eval eval (times (atom e2) (atom e3))  -- 6

-- 11 = 0
#eval eval (plus (atom e1) (atom e1))  -- 0

-- 1(경계)의 이중 역할
-- +에서: 항등원
theorem one_plus_identity (a : Expr) : eval (plus (atom e1) a) = eval a := by
  simp [eval]

-- ×에서: 소멸자
theorem one_times_annihilator (a : Expr) : eval (times (atom e1) a) = 0 := by
  simp [eval]

-----------------------------------------------------
-- 2. 교환 (순서 없음의 비용)
-----------------------------------------------------

theorem plus_comm (a b : Expr) : eval (plus a b) = eval (plus b a) := by
  simp [eval, Nat.add_comm]

theorem times_comm (a b : Expr) : eval (times a b) = eval (times b a) := by
  simp [eval, Nat.mul_comm]

-----------------------------------------------------
-- 3. 결합 (괄호 없음의 비용)
-----------------------------------------------------

theorem plus_assoc (a b c : Expr) :
  eval (plus (plus a b) c) = eval (plus a (plus b c)) := by
  simp [eval, Nat.add_assoc]

theorem times_assoc (a b c : Expr) :
  eval (times (times a b) c) = eval (times a (times b c)) := by
  simp [eval, Nat.mul_assoc]

-- 213에서는 이 증명들이 필요 없다.
-- 순서가 없으니 교환은 자동, 괄호가 없으니 결합도 자동.
-- Lean에서 증명해야 하는 건 매체의 비용이다.

-----------------------------------------------------
-- 4. 모든 자연수 ≥ 2의 표현 가능성
-----------------------------------------------------

-- 2, 3: 원자
-- 4 = 22
-- 5 = 213 (2+3)
-- 6 = 23
-- 7 = 22+3 (2²+3)
-- 8 = 222
-- 9 = 33
-- 10 = 22+23 (2²+2×3)... 아니, 더 간단하게: 2+2+3+3

def expr2 := atom e2
def expr3 := atom e3
def expr4 := times (atom e2) (atom e2)
def expr5 := plus (atom e2) (atom e3)
def expr6 := times (atom e2) (atom e3)
def expr7 := plus (times (atom e2) (atom e2)) (atom e3)
def expr8 := times (times (atom e2) (atom e2)) (atom e2)
def expr9 := times (atom e3) (atom e3)
def expr10 := plus (plus (atom e2) (atom e2)) (times (atom e2) (atom e3))

#eval eval expr2   -- 2
#eval eval expr3   -- 3
#eval eval expr4   -- 4
#eval eval expr5   -- 5
#eval eval expr6   -- 6
#eval eval expr7   -- 7
#eval eval expr8   -- 8
#eval eval expr9   -- 9
#eval eval expr10  -- 10

-- 각각 증명
theorem t2 : eval expr2 = 2 := by rfl
theorem t3 : eval expr3 = 3 := by rfl
theorem t4 : eval expr4 = 4 := by rfl
theorem t5 : eval expr5 = 5 := by rfl
theorem t6 : eval expr6 = 6 := by rfl
theorem t7 : eval expr7 = 7 := by rfl
theorem t8 : eval expr8 = 8 := by rfl
theorem t9 : eval expr9 = 9 := by rfl
theorem t10 : eval expr10 = 10 := by rfl

-----------------------------------------------------
-- 5. 가산 원자 정리
-- n ≥ 4이면 n = a + b (a, b ≥ 2)로 분해 가능
-----------------------------------------------------

theorem additive_atom_2 : ¬ ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = 2 := by omega
theorem additive_atom_3 : ¬ ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = 3 := by omega
theorem not_atom_4 : ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = 4 := ⟨2, 2, by omega, by omega, by omega⟩
theorem not_atom_5 : ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = 5 := ⟨2, 3, by omega, by omega, by omega⟩

-- 일반화: n ≥ 4이면 분해 가능
theorem not_atom_ge4 (n : Nat) (h : n ≥ 4) : ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = n :=
  ⟨2, n - 2, by omega, by omega, by omega⟩

-----------------------------------------------------
-- 6. 고정점: C(3,2) = 3
-----------------------------------------------------

-- 무순 쌍의 개수 C(n,2) = n(n-1)/2
def choose2 (n : Nat) : Nat := n * (n - 1) / 2

#eval choose2 1  -- 0 (죽음)
#eval choose2 2  -- 1 (죽음)
#eval choose2 3  -- 3 (자기지속!)
#eval choose2 4  -- 6 (폭발)
#eval choose2 5  -- 10 (폭발)

-- 고정점: choose2(n) = n의 해
theorem fixed_point_3 : choose2 3 = 3 := by native_decide

-- 2는 고정점이 아님
theorem not_fixed_2 : choose2 2 ≠ 2 := by native_decide

-- 4는 고정점이 아님
theorem not_fixed_4 : choose2 4 ≠ 4 := by native_decide

-- 1은 고정점이 아님
theorem not_fixed_1 : choose2 1 ≠ 1 := by native_decide

-- 0은 고정점 (자명한 해: 아무것도 없으면 아무것도 없다)
-- 비자명 고정점은 3뿐
#eval (List.range 100).filter (fun n => choose2 n == n)
-- [0, 3]만 나와야 함

-----------------------------------------------------
-- 7. 1의 이중 역할이 0의 성질과 일치함을 증명
-----------------------------------------------------

-- 수학에서 0의 두 성질:
-- (a) 덧셈 항등원: 0 + x = x
-- (b) 곱셈 소멸자: 0 × x = 0

-- 213에서 1(경계)의 두 성질:
-- (a) +에서 항등: 1이 +에 참여하면 변화 없음
-- (b) ×에서 소멸: 1이 ×에 참여하면 전부 사라짐

-- 이 둘이 같음:
theorem e1_is_zero_add (a : Expr) : eval (plus (atom e1) a) = eval a := by
  simp [eval]

theorem e1_is_zero_mul (a : Expr) : eval (times (atom e1) a) = 0 := by
  simp [eval]

-- 213에서의 1 = 수학에서의 0.
-- 이건 넣은 것이 아니라 나온 것이다.
-- "1은 내용 없음"만 넣었더니 0의 대수적 성질이 자동으로 따라왔다.

-----------------------------------------------------
-- 8. 분배법칙: 이건 넣었나, 나왔나?
-----------------------------------------------------

theorem distrib (a b c : Expr) :
  eval (times a (plus b c)) = eval (plus (times a b) (times a c)) := by
  simp [eval, Nat.mul_add]

-- 분배법칙은 Nat.mul_add에서 왔다.
-- 이건 213에서 나온 것인가, Nat의 성질인가?
-- eval이 Nat으로 번역하므로, Nat의 성질을 물려받는다.
-- 213 자체에서 분배법칙이 나오는지는 별도 질문이다.

-----------------------------------------------------
-- 9. 자기참조: 213을 213으로 기술
-----------------------------------------------------

-- 213의 원소 개수
#eval (3 : Nat)  -- E의 constructor 수 = 3

-- 213의 "내용 있는" 원소 개수
-- e1은 내용 없음(0), e2와 e3만 내용 있음
-- 내용 있는 원소 = 2개

-- 213을 기술하는 데 필요한 것:
-- 원소 3개를 구분(2)하고 경계(1)를 놓는다
-- 이 행위 자체가 213이다

-- E의 원소 수
def E_count : Nat := 3

-- E의 내용 있는 원소 수
def E_content_count : Nat := 2

-- E의 경계 원소 수
def E_boundary_count : Nat := 1

-- 자기참조 확인
theorem self_ref : E_count = E_content_count + E_boundary_count := by rfl
-- 3 = 2 + 1. 213 = 213.
