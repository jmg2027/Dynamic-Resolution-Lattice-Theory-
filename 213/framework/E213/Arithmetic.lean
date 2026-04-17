import E213.Axiom

/-
  구분의 산술: ×, +, =. (이 순서가 근본적.)

  × = 비교(섞음). 가장 기본. 둘을 섞어 다름을 드러냄.
  + = 합성. ×의 결과들을 모음. × 이후에만 의미 있음.
  = = 판정. ×의 차이를 현재 해상도에서 무시. 가장 나중.
  순서: × → + → =. (표준의 = → + → × 와 정반대.)
-/

-- ═══ × = rel: 가장 기본 ═══
-- a × b = rel a b. 비교. 다름을 만들고 드러냄.
-- 쌍 하나만 있어도 × 가능. 독립적.

-- ═══ + = 결과 모음 ═══
-- ×의 결과 세 개를 triple로 묶음.
-- relify = (모든 쌍에 ×) then (결과를 triple로 +).
-- × 없이 +할 대상이 없음. × 에 의존.

theorem relify_is_mul_then_add (rel : α → α → α) (t : Triple α) :
    relify rel t = ⟨rel t.x t.y, rel t.x t.z, rel t.y t.z⟩ := rfl

-- ═══ = = 해상도 의존 판정 ═══
-- ×로 차이를 봤는데, 현재 chain level에서 무시 가능이면 =.
-- chain 더 돌리면(해상도↑) = 이 깨질 수 있음.
-- chain 덜 돌리면(해상도↓) 더 많은 것이 =.

-- = 이 ×에 의존: "같다"의 기준 = 해상도 = ×의 반복 횟수.
-- 표준 수학은 해상도를 ∞로 고정 → = 이 공리처럼 보임.
-- 213: 해상도가 변수. = 은 파생.

-- ═══ chain에서의 역할 ═══

-- chain k = (×후+)^k.
-- 매 단계: × (비교) → + (합성) → 다음 level.
-- = 은 각 level에서 "여기서 멈춰도 되는가" 판정.

theorem lv0 (rel : α → α → α) (t : Triple α) :
    chain rel t 0 = t := rfl
theorem lv1 (rel : α → α → α) (t : Triple α) :
    chain rel t 1 = relify rel t := rfl
theorem lv2 (rel : α → α → α) (t : Triple α) :
    chain rel t 2 = relify rel (relify rel t) := rfl

-- ═══ ×의 닫힘 (Triple만) ═══
-- 2개: × 한 번 → 1개. 닫히지 않음.
-- 3개: × 세 번 → 3개 = triple. 닫힘!
-- 4개: × 여섯 번 → 6개. 닫히지 않음.

-- ═══ 분배법칙 = ×와 +의 관계 ═══
-- relify = ×를 triple에 분배 후 +로 묶음.
-- 표준: a × (b + c) = a×b + a×c.
-- 213: ×{a,b,c} = +(a×b, a×c, b×c).
-- ×가 내용, +가 형식. ×가 먼저, +가 나중.

-- ═══ 의미론적 소인수분해 ═══
-- × = 원소. 더 분해 불가.
-- + = ×의 합성. 분해하면 ×.
-- = = ×+의 해상도 판정. 분해하면 ×와 +.
-- 근본 순서: × ≺ + ≺ =.

-- ═══ 요약 ═══
structure OpOrder where
  mul_is_rel : ∀ (rel : Nat → Nat → Nat) (t : Triple Nat),
    relify rel t = ⟨rel t.x t.y, rel t.x t.z, rel t.y t.z⟩
  closed_at_3 : pairs 3 = 3
  chain_is_iter : ∀ (rel : Nat → Nat → Nat) (t : Triple Nat),
    chain rel t 1 = relify rel t

theorem op_order : OpOrder where
  mul_is_rel := fun _ _ => rfl
  closed_at_3 := by native_decide
  chain_is_iter := fun _ _ => rfl
