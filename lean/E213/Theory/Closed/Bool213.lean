import E213.Theory.Closed.FoldRaw

/-!
# Theory.Closed.Bool213 — closed-universe Bool

Bool 을 외부 type 으로 빌리지 않고 Raw 의 특정 두 모양으로 인코딩.
operation 들도 Raw → Raw 또는 Raw → Raw → Raw 로 닫혀 있음.

## 무한히 많은 Bool213 (Z, C 쌍 자유)

기본 선택:
  - `Bool213.MethodA`: T = Raw.a, F = Raw.b
  - `Bool213.MethodB`: T = Raw.b, F = Raw.a (swap된 것)

다른 (T, F) 쌍 (예: T = `slash a b`, F = `a`) 도 같은 대수 구조를 줌
— 마지막에 NumberingSystem-style 메타 패턴으로 정리.
-/

namespace E213.Theory.Closed.Bool213

open E213.Theory E213.Theory.Closed

/-! ### Method A: T = a, F = b (canonical) -/

/-- "true" 의 Raw 표현 (Method A). -/
def T : Raw := Raw.a

/-- "false" 의 Raw 표현 (Method A). -/
def F : Raw := Raw.b

/-- 두 표현은 다른 Raw — Raw.a, Raw.b 는 서로 다른 canonical Tree. -/
theorem T_ne_F : T ≠ F := by
  unfold T F
  intro h
  -- Raw 는 Subtype { t : Tree // canonical }; 두 인스턴스의 .val 이 다름
  have hval : (Raw.a.val) = (Raw.b.val) := congrArg Subtype.val h
  exact E213.Theory.Internal.Tree.noConfusion hval

end E213.Theory.Closed.Bool213

namespace E213.Theory.Closed.Bool213

open E213.Theory E213.Theory.Closed

/-! ### Bool213 operations (Raw → Raw 또는 Raw² → Raw 닫힘) -/

/-- 표현이 valid Bool213 인지 — `T` 또는 `F`. -/
def isBool (r : Raw) : Bool :=
  decide (r = T) || decide (r = F)

/-- `not` = swap.  swap a = b, swap b = a → 기존 Raw.swap 그대로. -/
def not : Raw → Raw := Raw.swap

theorem not_T : not T = F := rfl
theorem not_F : not F = T := rfl

/-- `not (not r) = r` — Raw.swap 의 involution 직접 차용. -/
theorem not_not (r : Raw) : not (not r) = r := Raw.swap_swap r

/-- `and` — table 정의로 Raw 쌍에서 Raw 로. T = a, F = b 로 인코딩하는
    Method A 에서 `and x y = T iff x = T ∧ y = T`. -/
def and (x y : Raw) : Raw :=
  if decide (x = T) ∧ decide (y = T) then T else F

theorem and_TT : and T T = T := by unfold and; decide
theorem and_TF : and T F = F := by unfold and; decide
theorem and_FT : and F T = F := by unfold and; decide
theorem and_FF : and F F = F := by unfold and; decide

/-- `and` 가 교환적 (모든 Raw 입력에 대해 — `if` 분기 항상 일치). -/
theorem and_comm (x y : Raw) : and x y = and y x := by
  unfold and
  by_cases hxT : x = T
  · subst hxT
    by_cases hyT : y = T
    · subst hyT; rfl
    · rw [if_neg, if_neg]
      · rintro ⟨h1, _⟩; exact hyT (of_decide_eq_true h1)
      · rintro ⟨_, h2⟩; exact hyT (of_decide_eq_true h2)
  · by_cases hyT : y = T
    · subst hyT
      rw [if_neg, if_neg]
      · rintro ⟨_, h2⟩; exact hxT (of_decide_eq_true h2)
      · rintro ⟨h1, _⟩; exact hxT (of_decide_eq_true h1)
    · rw [if_neg, if_neg]
      · rintro ⟨h1, _⟩; exact hyT (of_decide_eq_true h1)
      · rintro ⟨h1, _⟩; exact hxT (of_decide_eq_true h1)

end E213.Theory.Closed.Bool213
