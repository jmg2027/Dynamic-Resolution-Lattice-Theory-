import E213.Theory.Raw.Fold
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Slash
import E213.Theory.Raw.SwapSlash
import E213.Theory.Raw.Rec

/-!
# Theory.Closed.FoldRaw — endomorphic fold (closed universe)

Vision: 213 = closed universe. Raw가 곧 universe.  외부 type α (Bool,
Nat, Prop, ...) 에 의존하지 않고 모든 연산이 `Raw → Raw` 안에서 닫힘.

`foldRaw : Raw → Raw → (Raw → Raw → Raw) → Raw → Raw` —
endomorphic 카타모피즘. codomain 자체가 Raw.

이 파일은 closed-universe vision의 시범 — `foldRaw` 정의 + `swap`을
foldRaw 한 줄 인스턴스로 표현 + `swap (swap r) = r` PURE 증명.

## Why closed?

기존 `Raw.fold {α : Type}` 는 generic α 가능 — α := Bool/Nat/Prop/Lens 등
외부 type을 끌어옴. Lens equality / Prop equality 등에서 propext / funext /
Quot.sound 가 들어옴 (외부 type 의 동등성이 외부 axiom 의존).

`foldRaw` (= `Raw.fold (α := Raw)`) 는 codomain을 Raw 로 못박음 →
"view r1 = view r2" 가 항상 Raw eq → Tree.cmp decidable → ∅-axiom.

## Pattern

  - 기존: `Lens α := { base_a base_b : α, combine : α → α → α }`
  - 닫힌 우주: `(fa fb : Raw) (fc : Raw → Raw → Raw)` triple.

`fc`를 total function 으로 받기 위해 `slashOrSelf` 도우미 (Raw.slash가
`x ≠ y` 증명 요구하므로) 사용.
-/

namespace E213.Theory.Closed

open E213.Theory

/-- `Raw.slash` 의 total 변형: `x = y` 면 `x` 를 그대로 반환,
    아니면 canonical slash. closed universe 의 default fc. -/
def slashOrSelf (x y : Raw) : Raw :=
  if h : x = y then x else Raw.slash x y h

/-- `slashOrSelf` 가 두 인자가 다를 때 `Raw.slash` 와 일치. -/
theorem slashOrSelf_of_ne {x y : Raw} (h : x ≠ y) :
    slashOrSelf x y = Raw.slash x y h := by
  unfold slashOrSelf; rw [dif_neg h]

/-- `slashOrSelf x x = x`. -/
theorem slashOrSelf_self (x : Raw) : slashOrSelf x x = x := by
  unfold slashOrSelf; rw [dif_pos rfl]

end E213.Theory.Closed

namespace E213.Theory.Closed

open E213.Theory

/-! ### foldRaw — endomorphic fold (codomain = Raw) -/

/-- `foldRaw fa fb fc r` — 끝(leaf)에서 `fa`/`fb` 로 시작해
    slash 마다 `fc` 로 결합하면서 r의 골격을 따라 새 Raw를 만든다.
    α := Raw 인 `Raw.fold` 의 별명. -/
def foldRaw (fa fb : Raw) (fc : Raw → Raw → Raw) (r : Raw) : Raw :=
  Raw.fold fa fb fc r

theorem foldRaw_a (fa fb : Raw) (fc : Raw → Raw → Raw) :
    foldRaw fa fb fc Raw.a = fa := rfl

theorem foldRaw_b (fa fb : Raw) (fc : Raw → Raw → Raw) :
    foldRaw fa fb fc Raw.b = fb := rfl

/-- foldRaw 의 slash 케이스 — `fc` 가 symmetric 일 때
    `fc (foldRaw x) (foldRaw y)` 로 분해.  `Raw.fold_slash` 의 별명. -/
theorem foldRaw_slash (fa fb : Raw) (fc : Raw → Raw → Raw)
    (hsym : ∀ u v : Raw, fc u v = fc v u)
    (x y : Raw) (h : x ≠ y) :
    foldRaw fa fb fc (Raw.slash x y h)
      = fc (foldRaw fa fb fc x) (foldRaw fa fb fc y) :=
  Raw.fold_slash fa fb fc hsym x y h

end E213.Theory.Closed

namespace E213.Theory.Closed

open E213.Theory

/-! ### Demo: swap = foldRaw with (fa=b, fb=a, fc=slashOrSelf) -/

/-- `slashOrSelf` 가 symmetric — closed-universe combine 들이 일반적으로
    만족해야 하는 axiom-compliance 조건. -/
theorem slashOrSelf_comm (x y : Raw) :
    slashOrSelf x y = slashOrSelf y x := by
  unfold slashOrSelf
  by_cases h : x = y
  · subst h; rfl
  · rw [dif_neg h, dif_neg (Ne.symm h), Raw.slash_comm x y h]

/-- **Closed-universe swap**: `Raw.swap` 을 `foldRaw` 한 줄로 재표현.
    fa = b (a → b), fb = a (b → a), fc = slashOrSelf (재구성). -/
def swapClosed : Raw → Raw :=
  foldRaw Raw.b Raw.a slashOrSelf

theorem swapClosed_a : swapClosed Raw.a = Raw.b := rfl
theorem swapClosed_b : swapClosed Raw.b = Raw.a := rfl

/-- **Bridge**: 닫힌-우주 swap = 기존 `Raw.swap` 포인트별로 일치. -/
theorem swapClosed_eq_swap (r : Raw) : swapClosed r = Raw.swap r := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      -- LHS unfolds via foldRaw_slash (slashOrSelf is sym)
      rw [show swapClosed (Raw.slash x y h)
            = slashOrSelf (swapClosed x) (swapClosed y) from
          foldRaw_slash _ _ _ slashOrSelf_comm x y h]
      rw [ihx, ihy]
      -- RHS unfolds via Raw.swap_slash
      rw [Raw.swap_slash x y h]
      -- Now: slashOrSelf (Raw.swap x) (Raw.swap y) = Raw.slash ...
      have hne : Raw.swap x ≠ Raw.swap y :=
        fun e => h (Raw.swap_injective e)
      exact slashOrSelf_of_ne hne

/-- **Closed-universe swap_swap**: 모든 r 에 대해 `swap (swap r) = r`.
    foldRaw 표현으로부터 직접. -/
theorem swapClosed_swapClosed (r : Raw) :
    swapClosed (swapClosed r) = r := by
  rw [swapClosed_eq_swap, swapClosed_eq_swap, Raw.swap_swap]

end E213.Theory.Closed
