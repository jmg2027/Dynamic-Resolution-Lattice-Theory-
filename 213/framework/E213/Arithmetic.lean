import E213.Axiom

/-
  구분의 산술: +와 ×.

  + = 구분. 둘을 비교하여 관계 생성.
  × = 합성. +를 모든 쌍에 분배 (= relify).

  a+b 정의 → a≠b 판정 필요 → ab 관계 생성 필요 → 이것이 +.
  자기참조: + 없이 ≠ 불가, ≠ 없이 + 불가.
  해결: 3개에서 동시에. 세 +가 서로를 검증.
-/

-- + = rel: 이항 비교. 관계 하나 생성.
-- × = relify: +를 triple 전체에 분배. 새 triple 생성.

-- ═══ +의 조건 ═══

-- a + b가 유의미 ↔ a+b가 다른 관계와 구분됨.
-- n=2: a+b 하나뿐. 구분 대상 없음. 무의미한 +.
-- n=3: a+b, a+c, b+c 셋. 서로 구분됨. 유의미한 +.

-- ═══ ×의 정의 ═══

-- × {a,b,c} = {a+b, a+c, b+c}.
-- +를 모든 쌍에 적용. 이것이 relify.
-- 일반 분배법칙 a×(b+c) = ab+ac 의 원형.

-- 형식 확인: relify = + 세 번.
theorem product_is_three_sums (rel : α → α → α) (t : Triple α) :
    relify rel t = ⟨rel t.x t.y, rel t.x t.z, rel t.y t.z⟩ := rfl

-- ═══ ×의 닫힘 ═══

-- × 입력: Triple α. 출력: Triple α. 닫힘.
-- n=2: + 한 번 → α 하나. Pair α → α. 열림.
-- n=4: + 여섯 번 → 6개. Quad α → ???. 열림.
-- Triple만 닫힘. C(3,2) = 3.

-- ═══ + 와 × 의 독립성 ═══

-- +: 쌍 하나를 비교 (미시).
-- ×: 모든 쌍을 비교 (거시).
-- +의 결과를 모아야 ×. ×를 분해해야 +.
-- 환원 불가. 독립.

-- ═══ 체인 = ×의 반복 ═══

theorem chain_0 (rel : α → α → α) (t : Triple α) :
    chain rel t 0 = t := rfl

theorem chain_1 (rel : α → α → α) (t : Triple α) :
    chain rel t 1 = relify rel t := rfl

theorem chain_2 (rel : α → α → α) (t : Triple α) :
    chain rel t 2 = relify rel (relify rel t) := rfl

-- chain k = ×^k. +의 k중 분배. 매 단계 구조 보존.

-- ═══ 의미론적 소인수분해 ═══
-- +: 구분 (수평). ×: 합성 (수직). 이 둘이 소인수.
-- 분배법칙: ×후+ = +후×. relify 후 선택 = 선택 후 rel.

-- ═══ 정리 ═══

structure ArithmeticTheorem where
  sum_is_rel : ∀ (rel : Nat → Nat → Nat) (t : Triple Nat),
    relify rel t = ⟨rel t.x t.y, rel t.x t.z, rel t.y t.z⟩
  product_closed : pairs 3 = 3
  chain_unfold : ∀ (rel : Nat → Nat → Nat) (t : Triple Nat),
    chain rel t 1 = relify rel t

theorem arithmetic : ArithmeticTheorem where
  sum_is_rel := fun _ _ => rfl
  product_closed := by native_decide
  chain_unfold := fun _ _ => rfl
