-- 213 (완성본: 223 = 2²×3 = 12 공리)
--
-- 이 코드는 타입 매체에 쓰여 있다.
-- Lean은 타입 선언을 요구한다. 이것은 매체의 제약이지 213의 성질이 아니다.
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
-- 2. 223: 12개 공리
--
--    매체 비용 (동치관계):  1-3   (3개)
--    213 고유 내용:         4-9   (6개 = 23)
--    매체 비용 (합동):      10-11 (2개)
--    분배:                  12    (1개)
--    합계:                  12 = 2²×3 = 223
-----------------------------------------------------

inductive Equiv : Expr → Expr → Prop where
  -- [매체 비용: 동치관계] (3개)
  | refl (a : Expr) : Equiv a a                                            -- 1
  | symm {a b : Expr} : Equiv a b → Equiv b a                              -- 2
  | trans {a b c : Expr} : Equiv a b → Equiv b c → Equiv a c               -- 3
  -- [213 고유: 교환] (2개)
  | plus_comm (a b : Expr) : Equiv (plus a b) (plus b a)                    -- 4
  | times_comm (a b : Expr) : Equiv (times a b) (times b a)                 -- 5
  -- [213 고유: 결합] (2개)
  | plus_assoc (a b c : Expr) : Equiv (plus (plus a b) c)                   -- 6
                                       (plus a (plus b c))
  | times_assoc (a b c : Expr) : Equiv (times (times a b) c)                -- 7
                                        (times a (times b c))
  -- [213 고유: 경계의 성질] (2개)
  | plus_e1 (a : Expr) : Equiv (plus (atom e1) a) a                         -- 8
  | times_e1 (a : Expr) : Equiv (times (atom e1) a) (atom e1)               -- 9
  -- [매체 비용: 합동] (2개)
  | plus_cong {a a' b b' : Expr} :                                          -- 10
      Equiv a a' → Equiv b b' → Equiv (plus a b) (plus a' b')
  | times_cong {a a' b b' : Expr} :                                         -- 11
      Equiv a a' → Equiv b b' → Equiv (times a b) (times a' b')
  -- [분배: +와 ×의 연결] (1개)
  | distrib (a b c : Expr) :                                                -- 12
      Equiv (times a (plus b c)) (plus (times a b) (times a c))

infix:50 " ≈ " => Equiv

-----------------------------------------------------
-- 3. 편의 표기
-----------------------------------------------------

def e (x : E) : Expr := atom x
def e₁ := e e1
def e₂ := e e2
def e₃ := e e3

-----------------------------------------------------
-- 4. 기본 정리들
-----------------------------------------------------

-- 213 ≈ 312 (순서 없음)
theorem e213_eq_312 : plus e₂ (plus e₁ e₃) ≈ plus e₃ (plus e₁ e₂) := by
  apply Equiv.trans
  · exact Equiv.plus_cong (Equiv.refl e₂) (Equiv.plus_e1 e₃)
  · apply Equiv.trans
    · exact Equiv.plus_comm e₂ e₃
    · exact Equiv.symm (Equiv.plus_cong (Equiv.refl e₃) (Equiv.plus_e1 e₂))

-- 경계 성질
theorem boundary_plus (x : Expr) : plus e₁ x ≈ x := Equiv.plus_e1 x
theorem boundary_times (x : Expr) : times e₁ x ≈ e₁ := Equiv.times_e1 x
theorem plus_boundary (x : Expr) : plus x e₁ ≈ x :=
  Equiv.trans (Equiv.plus_comm x e₁) (Equiv.plus_e1 x)
theorem times_boundary (x : Expr) : times x e₁ ≈ e₁ :=
  Equiv.trans (Equiv.times_comm x e₁) (Equiv.times_e1 x)

-- 11 ≈ 1
theorem e11_eq_e1 : plus e₁ e₁ ≈ e₁ := Equiv.plus_e1 e₁

-----------------------------------------------------
-- 5. 분배법칙에서 따라나오는 것들
-----------------------------------------------------

-- 우분배: (a+b)×c ≈ a×c + b×c
theorem distrib_right (a b c : Expr) :
    times (plus a b) c ≈ plus (times a c) (times b c) := by
  apply Equiv.trans
  · exact Equiv.times_comm (plus a b) c
  · apply Equiv.trans
    · exact Equiv.distrib c a b
    · exact Equiv.plus_cong (Equiv.times_comm c a) (Equiv.times_comm c b)

-- 1×(a+b) ≈ 1 (소멸이 분배보다 강함)
theorem annihilate_plus (a b : Expr) :
    times e₁ (plus a b) ≈ e₁ := Equiv.times_e1 (plus a b)

-- 분배 후 소멸: 1×a + 1×b ≈ 1+1 ≈ 1
theorem annihilate_distrib (a b : Expr) :
    plus (times e₁ a) (times e₁ b) ≈ e₁ := by
  apply Equiv.trans
  · exact Equiv.plus_cong (Equiv.times_e1 a) (Equiv.times_e1 b)
  · exact Equiv.plus_e1 e₁

-- 이 둘이 정합적인지 확인:
-- 1×(a+b) ≈ 1  (직접 소멸)
-- 1×(a+b) ≈ 1×a + 1×b ≈ 1+1 ≈ 1  (분배 후 소멸)
-- 같은 결과. ✓
theorem annihilate_consistent (a b : Expr) :
    times e₁ (plus a b) ≈ plus (times e₁ a) (times e₁ b) :=
  Equiv.distrib e₁ a b

-----------------------------------------------------
-- 6. 고정점: 전단사 (Nat-free)
-----------------------------------------------------

-- E의 무순 쌍
inductive UPair where
  | mk : E → E → UPair
deriving Repr

-- 무순 쌍의 동치
def UPair.equiv : UPair → UPair → Prop
  | .mk a b, .mk c d => (a = c ∧ b = d) ∨ (a = d ∧ b = c)

-- 서로 다른가
def E.ne : E → E → Bool
  | e1, e1 => false | e2, e2 => false | e3, e3 => false
  | _, _ => true

-- 순방향: 무순 쌍 → E
def pair_to_E : UPair → E
  | .mk e1 e2 => e1 | .mk e2 e1 => e1
  | .mk e2 e3 => e2 | .mk e3 e2 => e2
  | .mk e1 e3 => e3 | .mk e3 e1 => e3
  | .mk e1 e1 => e1 | .mk e2 e2 => e2 | .mk e3 e3 => e3

-- 역방향: E → 무순 쌍
def E_to_pair : E → UPair
  | e1 => .mk e1 e2
  | e2 => .mk e2 e3
  | e3 => .mk e1 e3

-- 왕복 1: E → pair → E = id
theorem roundtrip_E (x : E) : pair_to_E (E_to_pair x) = x := by
  cases x <;> rfl

-- 왕복 2: pair → E → pair ≈ id (서로 다른 쌍에 대해)
-- UPair.equiv 하에서 왕복 성립
theorem roundtrip_pair_12 : UPair.equiv (E_to_pair (pair_to_E (.mk e1 e2))) (.mk e1 e2) := by
  simp [pair_to_E, E_to_pair, UPair.equiv]

theorem roundtrip_pair_23 : UPair.equiv (E_to_pair (pair_to_E (.mk e2 e3))) (.mk e2 e3) := by
  simp [pair_to_E, E_to_pair, UPair.equiv]

theorem roundtrip_pair_13 : UPair.equiv (E_to_pair (pair_to_E (.mk e1 e3))) (.mk e1 e3) := by
  simp [pair_to_E, E_to_pair, UPair.equiv]

-- 뒤집힌 경우도
theorem roundtrip_pair_21 : UPair.equiv (E_to_pair (pair_to_E (.mk e2 e1))) (.mk e2 e1) := by
  simp [pair_to_E, E_to_pair, UPair.equiv]

theorem roundtrip_pair_32 : UPair.equiv (E_to_pair (pair_to_E (.mk e3 e2))) (.mk e3 e2) := by
  simp [pair_to_E, E_to_pair, UPair.equiv]

theorem roundtrip_pair_31 : UPair.equiv (E_to_pair (pair_to_E (.mk e3 e1))) (.mk e3 e1) := by
  simp [pair_to_E, E_to_pair, UPair.equiv]

-- 전단사 완성: E ↔ {서로 다른 무순 쌍} (양방향 왕복)
-- 숫자를 세지 않고, 대응이 존재함을 보였다.
-- 이것이 C(3,2) = 3의 Nat-free 버전이다.

-----------------------------------------------------
-- 7. 자기참조
-----------------------------------------------------

def content_elements : List E := [e2, e3]
def boundary_elements : List E := [e1]
def all_elements : List E := [e1, e2, e3]

-- 3 = 2 + 1 (List.length는 Nat이지만, 이건 매체 비용)
theorem self_ref :
  all_elements.length = content_elements.length + boundary_elements.length := by rfl

-----------------------------------------------------
-- 8. 공리 개수의 자기기술
-----------------------------------------------------

-- 매체 비용 공리: 1-3, 10-11 = 213개 = 2+3 = 5
-- 213 고유 공리: 4-9 = 23개 = 2×3 = 6
-- 분배 공리: 12 = 1개
-- 총 공리: 223개 = 2²×3 = 12

-- 공리 분류를 E로 표현:
-- 매체 비용 (동치 3개):      e3 (3)
-- 213 고유 내용 (6개):        times e₂ e₃ (23 = 6)
-- 매체 비용 (합동 2개):       e2 (2)
-- 분배 (1개):                e1 (1... 하지만 e1은 경계=0)

-- 총 공리 = 3 + 6 + 2 + 1 = 12 = 2²×3
-- 213 표기: 223

-----------------------------------------------------
-- 9. 열린 질문
-----------------------------------------------------

-- 역원: e₂에 대해 plus e₂ x ≈ e₁인 x가 E 안에 존재하는가?
-- 존재하지 않음을 보일 수 있다 (e1, e2, e3 어느 것도 안 됨).
-- 이는 213이 반환(semiring)이지 환(ring)이 아님을 의미한다.
-- 음수를 만들려면 E를 확장해야 하고, 그건 213이 아니다.

-- 연속체: 213에서 ℝ이나 ℂ로 가는 경로?
-- 현재 213은 이산적. 2와 3 사이에 "사이"가 없다.
-- 연속체가 필요하면 새 구조가 필요하다.

-- 자기참조의 한계: 213이 자기 자신에 대해 증명할 수 없는 것이 있는가?
-- Gödel적 질문. Equiv가 결정가능한지조차 열려있다.
