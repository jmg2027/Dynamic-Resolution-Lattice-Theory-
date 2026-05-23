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

Originally `Theory/Raw/FoldRaw.lean` — Closed/
directory companion.
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

/-- Total variant of `Raw.slash`: if `x = y`, return `x`; otherwise
    take the canonical slash.  Default `fc` for closed-universe
    catamorphisms. -/
def slashOrSelf (x y : Raw) : Raw :=
  if h : x = y then x else Raw.slash x y h

/-- When the two arguments differ, `slashOrSelf` agrees with
    `Raw.slash`. -/
theorem slashOrSelf_of_ne {x y : Raw} (h : x ≠ y) :
    slashOrSelf x y = Raw.slash x y h := by
  unfold slashOrSelf; rw [dif_neg h]

/-- `slashOrSelf x x = x`. -/
theorem slashOrSelf_self (x : Raw) : slashOrSelf x x = x := by
  unfold slashOrSelf; rw [dif_pos rfl]

/-! ### foldRaw — endomorphic fold (codomain = Raw) -/

/-- `foldRaw fa fb fc r` — starting from leaves with `fa`/`fb`,
    combine via `fc` at every slash, traversing `r`'s skeleton to
    build a new Raw.  Alias for `Raw.fold` at `α := Raw`. -/
def foldRaw (fa fb : Raw) (fc : Raw → Raw → Raw) (r : Raw) : Raw :=
  Raw.fold fa fb fc r

/-- `foldRaw`'s atomic cases are definitional (`foldRaw fa fb fc
    Raw.a = fa` and `Raw.b = fb` by `rfl`); the slash case is
    `Raw.fold_slash` lifted to `foldRaw`. -/
theorem foldRaw_slash (fa fb : Raw) (fc : Raw → Raw → Raw)
    (hsym : ∀ u v : Raw, fc u v = fc v u)
    (x y : Raw) (h : x ≠ y) :
    foldRaw fa fb fc (Raw.slash x y h)
      = fc (foldRaw fa fb fc x) (foldRaw fa fb fc y) :=
  Raw.fold_slash fa fb fc hsym x y h

/-! ### Demo: swap = foldRaw with (fa=b, fb=a, fc=slashOrSelf) -/

/-- `slashOrSelf` is symmetric — the axiom-compliance condition that
    closed-universe combines must generally satisfy. -/
theorem slashOrSelf_comm (x y : Raw) :
    slashOrSelf x y = slashOrSelf y x := by
  unfold slashOrSelf
  by_cases h : x = y
  · subst h; rfl
  · rw [dif_neg h, dif_neg (Ne.symm h), Raw.slash_comm x y h]

/-- **Closed-universe swap**: `Raw.swap` expressed in one line via
    `foldRaw`.  `fa = b` (a → b), `fb = a` (b → a), `fc =
    slashOrSelf` (reconstruct). -/
def swapClosed : Raw → Raw :=
  foldRaw Raw.b Raw.a slashOrSelf

theorem swapClosed_a : swapClosed Raw.a = Raw.b := rfl
theorem swapClosed_b : swapClosed Raw.b = Raw.a := rfl

/-- **Bridge**: closed-universe swap equals the existing `Raw.swap`
    pointwise. -/
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

/-- **Closed-universe swap_swap**: `swap (swap r) = r` for every r.
    Direct from the `foldRaw` representation. -/
theorem swapClosed_swapClosed (r : Raw) :
    swapClosed (swapClosed r) = r := by
  rw [swapClosed_eq_swap, swapClosed_eq_swap, Raw.swap_swap]

/-! ### slashOrSelf collapse characterisation (, iteration #16)

When does `slashOrSelf x y = y`?  Only when `x = y` (the diagonal
case).  Otherwise the result is `Raw.slash x y h`, which by
`Raw.slash_ne_right` is distinct from `y`. -/

/-- `slashOrSelf x y ≠ y` whenever `x ≠ y`.  Useful for chain
    non-collapse arguments. -/
theorem slashOrSelf_ne_of_ne (x y : Raw) (hxy : x ≠ y) :
    slashOrSelf x y ≠ y := by
  rw [slashOrSelf_of_ne hxy]
  exact E213.Theory.Raw.slash_ne_right _ _ hxy

/-- `slashOrSelf x y = y ↔ x = y` — biconditional collapse
    characterisation.  Reverse direction is `slashOrSelf_self`. -/
theorem slashOrSelf_eq_y_iff (x y : Raw) :
    slashOrSelf x y = y ↔ x = y := by
  constructor
  · intro h
    by_cases hxy : x = y
    · exact hxy
    · rw [slashOrSelf_of_ne hxy] at h
      exact absurd h (E213.Theory.Raw.slash_ne_right _ _ hxy)
  · intro h
    subst h
    exact slashOrSelf_self x

end E213.Theory.Raw.Endomorphic
