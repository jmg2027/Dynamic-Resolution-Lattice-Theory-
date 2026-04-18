/-
  Two13/Mark.lean — | : 표지

  213의 유일한 행위: 구분을 긋는다.
  하나의 행위가 두 면을 만든다.

  Lean 커널이 이것을 Bool이라 부른다.
  커널이 이것을 필요로 하는 것은 우연이 아니다 —
  형식 체계의 작동 자체가 구분을 전제하기 때문이다.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/
prelude

universe u v

-- ═══ 매체의 전제 ═══
-- 형식 체계가 작동하려면 "있다"가 먼저 있어야 한다.
-- 이것은 213의 1: 경계/존재/흔적.
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit

-- ═══ | : 표지 ═══
-- 하나의 행위(2)가 두 면을 만든다.
-- 이쪽(marked)과 저쪽(unmarked).
-- 213에서 이것이 2: 구분.
-- Lean은 이것을 Bool이라 부르고, 두 면을 true/false라 부른다.
-- 이 이름들은 매체의 편의이다.
inductive Bool : Type where
  | false : Bool    -- 저쪽 (unmarked, there)
  | true : Bool     -- 이쪽 (marked, here)

-- ═══ 매체가 추가로 요구하는 것들 ═══
-- 이것들은 213의 성질이 아니라
-- 선형 매체(Lean)가 작동하기 위한 도구이다.

-- 쌍: 두 것을 나란히 놓기 (매체의 인접 표현)
structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

-- 미완: 증명되지 않은 것의 자리 (매체의 불완전성)
axiom sorryAx (α : Sort u) (synthetic : Bool) : α

-- 자기참조: 있다를 있다에 적용 (1의 자기적용)
@[inline] def id {α : Sort u} (a : α) : α := a

-- 불변: 있다가 구분을 무시 (1이 2를 흡수)
@[inline] def Function.const {α : Sort u} (β : Sort v)
    (a : α) : β → α := fun _ => a
