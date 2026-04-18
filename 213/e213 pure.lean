-- 213 (Nat 없는 버전)
--
-- 이 코드는 타입 매체에 쓰여 있다.
-- Nat으로의 번역 없이 213 안에서만 작업한다.

inductive E where
  | e1 : E
  | e2 : E
  | e3 : E
deriving Repr, BEq, DecidableEq

open E

-----------------------------------------------------
-- 1. Expr: 213의 표현 (매체 제약으로 트리 형태)
-----------------------------------------------------

inductive Expr where
  | atom : E → Expr
  | plus : Expr → Expr → Expr   -- 1이 사이에 있음
  | times : Expr → Expr → Expr  -- 1이 사이에 없음
deriving Repr, BEq

open Expr

-----------------------------------------------------
-- 2. 동치 관계: 순서 없음을 Expr 위에서 직접 정의
--    213에서는 자동인 것을 매체 비용으로 증명한다.
-----------------------------------------------------

inductive Equiv : Expr → Expr → Prop where
  -- 반사
  | refl (a : Expr) : Equiv a a
  -- 대칭
  | symm {a b : Expr} : Equiv a b → Equiv b a
  -- 추이
  | trans {a b c : Expr} : Equiv a b → Equiv b c → Equiv a c
  -- 순서 없음 (교환)
  | plus_comm (a b : Expr) : Equiv (plus a b) (plus b a)
  | times_comm (a b : Expr) : Equiv (times a b) (times b a)
  -- 괄호 없음 (결합)
  | plus_assoc (a b c : Expr) : Equiv (plus (plus a b) c) (plus a (plus b c))
  | times_assoc (a b c : Expr) : Equiv (times (times a b) c) (times a (times b c))
  -- 1(경계)의 성질: +에서 사라짐
  | plus_e1 (a : Expr) : Equiv (plus (atom e1) a) a
  -- 1(경계)의 성질: ×에서 소멸
  | times_e1 (a : Expr) : Equiv (times (atom e1) a) (atom e1)
  -- 합동 (내부 동치 전파)
  | plus_cong {a a' b b' : Expr} : Equiv a a' → Equiv b b' → Equiv (plus a b) (plus a' b')
  | times_cong {a a' b b' : Expr} : Equiv a a' → Equiv b b' → Equiv (times a b) (times a' b')

infix:50 " ≈ " => Equiv

-----------------------------------------------------
-- 3. 편의 표기
-----------------------------------------------------

def e (x : E) : Expr := atom x
def e₁ := e e1
def e₂ := e e2
def e₃ := e e3

-----------------------------------------------------
-- 4. Nat 없이 증명할 수 있는 것들
-----------------------------------------------------

-- 213 ≈ 312 (순서 없음)
-- 경로: 2+(1+3) ≈ 2+3 ≈ 3+2 ≈ 3+(1+2)
theorem e213_eq_312 : plus e₂ (plus e₁ e₃) ≈ plus e₃ (plus e₁ e₂) := by
  apply Equiv.trans
  · -- 2+(1+3) ≈ 2+3  (1이 +에서 사라짐)
    exact Equiv.plus_cong (Equiv.refl e₂) (Equiv.plus_e1 e₃)
  · apply Equiv.trans
    · -- 2+3 ≈ 3+2  (교환)
      exact Equiv.plus_comm e₂ e₃
    · -- 3+2 ≈ 3+(1+2)  (1을 다시 넣음, 역방향)
      exact Equiv.symm (Equiv.plus_cong (Equiv.refl e₃) (Equiv.plus_e1 e₂))

-- 1+x ≈ x (경계는 더해도 변화 없음)
theorem boundary_plus (x : Expr) : plus e₁ x ≈ x :=
  Equiv.plus_e1 x

-- 1×x ≈ 1 (경계와 융합하면 소멸)
theorem boundary_times (x : Expr) : times e₁ x ≈ e₁ :=
  Equiv.times_e1 x

-- x+1 ≈ x (교환 + 경계)
theorem plus_boundary (x : Expr) : plus x e₁ ≈ x :=
  Equiv.trans (Equiv.plus_comm x e₁) (Equiv.plus_e1 x)

-- x×1 ≈ 1 (교환 + 소멸)
theorem times_boundary (x : Expr) : times x e₁ ≈ e₁ :=
  Equiv.trans (Equiv.times_comm x e₁) (Equiv.times_e1 x)

-- 11 ≈ 1 (0+0 = 0)
theorem e11_eq_e1 : plus e₁ e₁ ≈ e₁ :=
  Equiv.plus_e1 e₁

-----------------------------------------------------
-- 5. 고정점: Nat 없이 표현
--    "E의 무순 쌍의 집합은 E와 같은 크기"
-----------------------------------------------------

-- E의 무순 쌍
inductive UPair where
  | mk : E → E → UPair  -- 순서 없음이므로 mk a b = mk b a로 취급
deriving Repr

-- 무순 쌍의 동치
def UPair.equiv : UPair → UPair → Prop
  | .mk a b, .mk c d => (a = c ∧ b = d) ∨ (a = d ∧ b = c)

-- E에서 서로 다른 무순 쌍 (a ≠ b인 것만)
def distinct_pairs : List UPair :=
  [UPair.mk e1 e2, UPair.mk e2 e3, UPair.mk e1 e3]

-- E의 원소 목록
def elements : List E := [e1, e2, e3]

-- 둘 다 3개
theorem fixed_point : distinct_pairs.length = elements.length := by rfl

-----------------------------------------------------
-- 6. 자기참조: E 안에서 E를 기술
-----------------------------------------------------

-- E의 원소 중 "내용 있는 것" (≠ e1)
def content_elements : List E := [e2, e3]

-- E의 원소 중 "경계" (= e1)
def boundary_elements : List E := [e1]

-- 자기참조: 전체 = 내용 + 경계
theorem self_ref :
  elements.length = content_elements.length + boundary_elements.length := by rfl
-- 3 = 2 + 1. 아직 Nat이지만, 이건 List.length의 귀결.

-----------------------------------------------------
-- 7. 전사 대응: 무순 쌍 → E
--    고정점의 구체적 실현
-----------------------------------------------------

-- 각 무순 쌍을 E 원소에 대응
def pair_to_E : UPair → E
  | .mk e1 e2 => e1
  | .mk e2 e3 => e2
  | .mk e1 e3 => e3
  -- 순서 뒤집힌 경우
  | .mk e2 e1 => e1
  | .mk e3 e2 => e2
  | .mk e3 e1 => e3
  -- 같은 원소 쌍 (자기구분 불가)
  | .mk e1 e1 => e1
  | .mk e2 e2 => e2
  | .mk e3 e3 => e3

-- 역방향: E → 무순 쌍
def E_to_pair : E → UPair
  | e1 => .mk e1 e2
  | e2 => .mk e2 e3
  | e3 => .mk e1 e3

-- 왕복 확인 (E → pair → E)
theorem roundtrip_E (x : E) : pair_to_E (E_to_pair x) = x := by
  cases x <;> rfl

-----------------------------------------------------
-- 8. Nat을 쓰지 않고 "크기"를 말하는 방법
--    E와 UPair(서로 다른 것만) 사이의 전단사
-----------------------------------------------------

-- 이 전단사 자체가 "C(3,2) = 3"의 Nat-free 버전이다.
-- 숫자를 세지 않고, 대응이 존재함을 보인다.

-----------------------------------------------------
-- 9. 열린 질문들
-----------------------------------------------------

-- 분배법칙을 Equiv에 추가해야 하는가, 아니면 도출되는가?
-- Nat 없이 분배법칙은 별도 공리로 추가해야 한다:
-- times a (plus b c) ≈ plus (times a b) (times a c)
-- 이건 213에서 "나오는" 것인가 "넣는" 것인가?

-- 역원: 어떤 x에 대해 plus x x' ≈ e₁인 x'가 존재하는가?
-- Nat에서는 자연수라 역원이 없다.
-- 213에서는? e₁ = 0이고, 음수가 없으면 역원도 없다.
-- 음수를 만들려면 새 원소가 필요한가, 아니면 213 안에 이미 있는가?
