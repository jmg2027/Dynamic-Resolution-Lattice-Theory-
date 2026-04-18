import Init

/-
  RawAxiom v3: 타입이 a/a를 거부.

  / 는 x ≠ y 증명이 있을 때만 적용 가능.
  a/a는 컴파일 안 됨. exception도 none도 아닌 타입 거부.
  자연 전개에서 a/a가 도달 불가능하므로, 타입이 이를 반영.
-/

inductive Raw where
  | atom : Fin 3 → Raw
  | rel : Raw → Raw → Raw
  deriving DecidableEq, Repr

-- / : x ≠ y 증명 필요.
def slash (x y : Raw) (h : x ≠ y) : Raw := .rel x y

-- ═══ Level 0 ═══

def a₀ : Raw := .atom 0
def b₀ : Raw := .atom 1

-- a ≠ b: 원자가 다름.
theorem a_ne_b : a₀ ≠ b₀ := by decide

-- a/b 구성:
def ab₀ : Raw := slash a₀ b₀ a_ne_b

-- a/a 시도:
-- def aa := slash a₀ a₀ ???
-- ??? 자리에 a₀ ≠ a₀ 증명을 넣어야 하는데 불가능.
-- 컴파일 거부. ✓

-- ═══ Level 1 ═══

-- a ≠ a/b:
theorem a_ne_ab : a₀ ≠ ab₀ := by decide
-- b ≠ a/b:
theorem b_ne_ab : b₀ ≠ ab₀ := by decide

-- 새 관계:
def aab₀ : Raw := slash a₀ ab₀ a_ne_ab
def bab₀ : Raw := slash b₀ ab₀ b_ne_ab

-- a/b를 다시 넣으면? ab₀/(ab₀)는?
-- slash ab₀ ab₀ ??? → ab₀ ≠ ab₀ 증명 불가. 거부. ✓

-- ═══ Level 2 ═══

-- 5개 객체: a₀, b₀, ab₀, aab₀, bab₀.
-- 이 중 서로 다른 쌍: C(5,2) = 10. 하지만 이미 있는 관계 제외.

-- 새 쌍들의 ≠ 증명:
theorem a_ne_aab : a₀ ≠ aab₀ := by decide
theorem a_ne_bab : a₀ ≠ bab₀ := by decide
theorem b_ne_aab : b₀ ≠ aab₀ := by decide
theorem b_ne_bab : b₀ ≠ bab₀ := by decide
theorem ab_ne_aab : ab₀ ≠ aab₀ := by decide
theorem ab_ne_bab : ab₀ ≠ bab₀ := by decide
theorem aab_ne_bab : aab₀ ≠ bab₀ := by decide

-- 새 관계 구성 (일부):
def a_aab : Raw := slash a₀ aab₀ a_ne_aab
def a_bab : Raw := slash a₀ bab₀ a_ne_bab
def b_aab : Raw := slash b₀ aab₀ b_ne_aab
def b_bab : Raw := slash b₀ bab₀ b_ne_bab
def ab_aab : Raw := slash ab₀ aab₀ ab_ne_aab
def ab_bab : Raw := slash ab₀ bab₀ ab_ne_bab
def aab_bab : Raw := slash aab₀ bab₀ aab_ne_bab

-- Level 2: 5 + 7 = 12개. (이미 있는 3개 관계 제외.)

-- ═══ 성질: 모든 ≠ 증명이 decide로 됨 ═══

-- Raw는 DecidableEq. 구조가 다르면 decide가 증명.
-- 자연 전개에서 만든 모든 객체는 트리가 다름 → decide 성공.
-- a/a 같은 것만 decide 실패 → 타입 거부.

-- ═══ 자연 전개의 구조 ═══

-- 매 레벨에서:
-- 1. 기존 객체들의 모든 ≠ 쌍 열거.
-- 2. 각 쌍에 slash 적용 (h : x ≠ y는 decide로 자동).
-- 3. 새 객체 중 기존과 같은 것 제거 (이것도 decide).
-- 4. 남은 것 = 새 객체. 다음 레벨로.

-- 이 과정에서 a/a는 절대 나오지 않음.
-- 타입이 보장. runtime이 아닌 compile time에서.

-- ═══ 이것이 의미하는 것 ═══

-- 등호(=)는 213 안에 없다.
-- ≠ 만 있다 (slash의 전제조건으로).
-- ≠ 는 decide로 증명됨 = 트리 구조 비교.
-- 이 비교는 "관찰자의 질문"이 아니라 "Lean HW의 타입 검사."
-- firmware가 HW(Lean)에 의존하는 부분: DecidableEq.

-- ═══ 정리: / 의 성질 (v3) ═══

def Raw.depth : Raw → Nat
  | .atom _ => 0
  | .rel a b => 1 + max a.depth b.depth

theorem v3_depth (x y : Raw) (h : x ≠ y) :
    (slash x y h).depth > x.depth := by
  simp [slash, Raw.depth]; omega

-- 단사:
theorem v3_injective (a b c d : Raw) (h1 : a ≠ b) (h2 : c ≠ d) :
    slash a b h1 = slash c d h2 → a = c ∧ b = d := by
  intro h; simp [slash] at h; exact h
