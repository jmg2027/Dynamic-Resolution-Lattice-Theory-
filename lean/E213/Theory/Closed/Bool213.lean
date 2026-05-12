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

namespace E213.Theory.Closed.Bool213

open E213.Theory E213.Theory.Internal E213.Theory.Closed

/-! ### Vertical-internal projection — Raw → Bool213 canonical form

leavesCountRaw 의 Bool 대응 (Nat213 와 같은 패턴):
임의 Raw 를 Bool213 의 두 canonical form (T, F) 중 하나로 collapse.

정의:  `booleanProj := Raw.fold T F and` — universal-T form,
       leaves 모두가 T 일 때만 T, 하나라도 F 면 F.

성질 (leavesCountRaw 와 동일):
  1. closure:    `booleanProj r ∈ {T, F}`  (모든 r 위)
  2. idempotence: `booleanProj² = booleanProj`  (모든 r 위)

이게 Bool 쪽 vertical-internal projection 의 정확한 표현.
Nat213 의 leavesCountRaw 와 같은 메타 패턴. -/

/-- Bool 쪽 vertical-internal projection — Raw → Bool213 canonical form. -/
def booleanProj : Raw → Raw := Raw.fold T F and

theorem booleanProj_T : booleanProj T = T := rfl
theorem booleanProj_F : booleanProj F = F := rfl

/-- `and` 의 출력은 정의로 항상 T 또는 F. -/
theorem and_isBool (x y : Raw) : and x y = T ∨ and x y = F := by
  unfold and
  split
  · left; rfl
  · right; rfl

/-- **Closure**: `booleanProj r ∈ {T, F}` for any Raw r.  Tree
    induction; slash 분기는 `and_isBool` 로 즉시 닫힘. -/
theorem booleanProj_isBool (r : Raw) :
    booleanProj r = T ∨ booleanProj r = F := by
  show Tree.fold T F and r.val = T ∨ Tree.fold T F and r.val = F
  generalize r.val = t
  induction t with
  | a => left; rfl
  | b => right; rfl
  | slash _ _ _ _ =>
      -- Tree.fold T F and (slash x y) = and (Tree.fold _ x) (Tree.fold _ y)
      show and _ _ = T ∨ and _ _ = F
      exact and_isBool _ _

/-- **Idempotence**: `booleanProj (booleanProj r) = booleanProj r`.
    closure 로부터 즉시 — booleanProj r 이 이미 T 또는 F. -/
theorem booleanProj_idempotent (r : Raw) :
    booleanProj (booleanProj r) = booleanProj r := by
  rcases booleanProj_isBool r with h | h
  · rw [h]; exact booleanProj_T
  · rw [h]; exact booleanProj_F

/-! ### Fixed-point 특성화 — Bool213 image 가 정확히 booleanProj 의 fixed point

세 도메인 (Nat213, Bool213, RawCut) 위 vertical-internal projection 이
모두 동일 메타 패턴: closure + idempotence + image-fixed-point ↔.
이 section 이 Bool213 쪽 ↔ 형태 완성. -/

/-- Raw r 이 Bool213 image 안 — `r = T` 또는 `r = F`. -/
def IsBool213 (r : Raw) : Prop := r = T ∨ r = F

/-- Bool213 면 booleanProj 의 fixed point. -/
theorem booleanProj_id_of_isBool213 (r : Raw) (h : IsBool213 r) :
    booleanProj r = r := by
  rcases h with hT | hF
  · rw [hT]; exact booleanProj_T
  · rw [hF]; exact booleanProj_F

/-- 역방향: booleanProj 의 fixed point 면 Bool213. -/
theorem isBool213_of_booleanProj_id (r : Raw) (h : booleanProj r = r) :
    IsBool213 r := by
  rcases booleanProj_isBool r with hT | hF
  · left; rw [← h]; exact hT
  · right; rw [← h]; exact hF

/-- **Fixed-point 특성화**: booleanProj 가 r 을 그대로 두는 것 ↔ r 이
    Bool213 ({T, F}).  Nat213 의 `leavesCountRaw_id_iff_isChain`,
    RawCut 의 `cutBooleanProj_id_iff_isBool` 와 평행. -/
theorem booleanProj_id_iff_isBool213 (r : Raw) :
    booleanProj r = r ↔ IsBool213 r :=
  ⟨isBool213_of_booleanProj_id r, booleanProj_id_of_isBool213 r⟩

end E213.Theory.Closed.Bool213

namespace E213.Theory.Closed.Bool213

open E213.Theory E213.Theory.Internal E213.Theory.Closed

/-! ### Boundary mapping — Bool213 → Lean Bool

Nat213 의 `value : Raw → Nat` 와 평행: Bool 쪽 boundary projection.

`boolValue := Raw.fold true false (·&&·)` — universal-true form,
모든 leaves 가 `a` 일 때만 true.

성질 (수직-외부 동형성):
  - `boolValue T = true`, `boolValue F = false`  (base)
  - `boolValue ∘ booleanProj = boolValue`         (commutativity with vertical-internal)

이게 G84 의 4 종류 동형성 중 #3 (수직-외부, Raw → Lean type) 의 Bool 사례.
Nat213 의 `value_leavesCountRaw_general` 와 정확히 평행. -/

/-- Boundary mapping — Bool213 universe → Lean Bool.  Universal-true form. -/
def boolValue : Raw → Bool := Raw.fold true false (· && ·)

theorem boolValue_T : boolValue T = true := rfl
theorem boolValue_F : boolValue F = false := rfl

/-- 보조: Tree induction — `Tree.fold T F and t` (with α = Raw) 의 값이
    항상 T 또는 F. -/
private theorem fold_T_F_and_isBool (t : Tree) :
    Tree.fold (α := Raw) T F and t = T ∨ Tree.fold (α := Raw) T F and t = F := by
  induction t with
  | a => left; rfl
  | b => right; rfl
  | slash _ _ _ _ => exact and_isBool _ _

/-- 보조: `and X Y` 의 boolValue 가 곱 — X, Y ∈ {T, F} 가정. -/
private theorem boolValue_and_of_isBool (x y : Raw)
    (hx : x = T ∨ x = F) (hy : y = T ∨ y = F) :
    boolValue (and x y) = (boolValue x && boolValue y) := by
  rcases hx with hxT | hxF
  · rcases hy with hyT | hyF
    · subst hxT; subst hyT; decide
    · subst hxT; subst hyF; decide
  · rcases hy with hyT | hyF
    · subst hxF; subst hyT; decide
    · subst hxF; subst hyF; decide

/-- **Boundary commutativity**: `boolValue (booleanProj r) = boolValue r`
    for any Raw r.  수직-외부 동형성 + 수직-내부 projection 의 호환. -/
theorem boolValue_booleanProj (r : Raw) :
    boolValue (booleanProj r) = boolValue r := by
  show boolValue (Tree.fold (α := Raw) T F and r.val)
     = Tree.fold true false (· && ·) r.val
  generalize r.val = t
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show boolValue (and (Tree.fold _ _ _ x) (Tree.fold _ _ _ y))
         = ((Tree.fold true false (· && ·) x) && (Tree.fold true false (· && ·) y))
      rw [boolValue_and_of_isBool _ _ (fold_T_F_and_isBool x) (fold_T_F_and_isBool y),
          ihx, ihy]

end E213.Theory.Closed.Bool213
