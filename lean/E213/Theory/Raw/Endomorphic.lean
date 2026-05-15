import E213.Theory.Raw.Rec
import E213.Theory.Raw.SwapSlash
import E213.Theory.Raw.Fold

/-!
# Theory.Raw.Endomorphic — endomorphic catamorphism on Raw

Endomorphic ( = Raw → Raw, codomain pinned to Raw) catamorphism +
companion total combinator `slashOrSelf`.  Genuine downstream
consumers in `Lens/Number/Nat213/{Raw, Bridge, NumberingSystem}`
use these for numbering-system isomorphism (Method A ↔ generic
NumberingSystem) and for the `succ` definition of `Nat213.Raw`.

  * `slashOrSelf x y` — total variant of `Raw.slash` (returns `x`
    when `x = y`, otherwise the canonical `Raw.slash x y _`).  Used
    as the default combine for closed-universe catamorphisms where
    a *total* `Raw → Raw → Raw` is required.
  * `foldRaw` — `Raw.fold` instantiated at `α := Raw`.  Naming is
    load-bearing: `Lens.Number.Nat213.NumberingSystem` proves that
    numbering-system conversion is *exactly* `foldRaw S.Z S.C
    slashOrSelf` (an *endomorphic* isomorphism, not a generic
    catamorphism).
  * `swapClosed` — demo: `Raw.swap = foldRaw Raw.b Raw.a slashOrSelf`
    with `swapClosed_eq_swap` bridge.  Confirms the closed-universe
    pattern subsumes the swap automorphism.

## History

Originally `Theory/Raw/FoldRaw.lean` (2026-05-13) — Closed/
directory companion.  2026-05-14: `Closed/` removed, FoldRaw
absorbed into `Theory/Raw/` as a sub-cluster (its catamorphism
output Nat213/Bool213/RawCut/NumberingSystem all moved to
Lens.Number).  2026-05-15: renamed `FoldRaw` → `Endomorphic` to
reflect actual role (endomorphic fold + numbering-system
isomorphism machinery, no longer a closed-universe "vision demo").

## Why endomorphic matters

Generic `Raw.fold {α : Type}` accepts any `α`.  At α = Lens-
quotient / Prop / Bool the equality of folds depends on external
axioms (propext, Quot.sound).  Pinning codomain to Raw
(`foldRaw`) keeps the entire reasoning ∅-axiom: Raw equality is
decidable via `Tree.cmp`.

## Pattern

  - generic: `Lens α := { base_a base_b : α, combine : α → α → α }`
  - endomorphic: `(fa fb : Raw) (fc : Raw → Raw → Raw)` triple.

`fc` must be total — hence `slashOrSelf` as default (handles `x =
y` collapse that `Raw.slash` rejects via `x ≠ y` argument).
-/

namespace E213.Theory.Raw.Endomorphic

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

end E213.Theory.Raw.Endomorphic
