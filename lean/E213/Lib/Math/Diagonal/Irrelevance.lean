import E213.LensCore
import E213.Prelude

/-!
# DiagonalIrrelevance: Diagonal behavior of Lens combine

Lean formalization of Note 34 §3-§4.

## Claims

- **Injective Lens**: if `Function.Injective L.view` then the diagonal
  value of `L.combine` has no effect on view (`diagonal_irrelevant`).
  If two Lenses agree on base and off-diagonal combine, their views agree
  on all of Raw.
- **Non-injective Lens**: if there is a view-collision
  (`∃ x ≠ y, view x = view y`), the diagonal value is directly hit in
  `view (slash x y h)` (`diagonal_reached_of_collision`).

The original text of Note 34 §4 ("PartialLens.view does not touch the
Raw-level diagonal") is inaccurate.  Whether the diagonal is hit is
determined by the injectivity of view.
-/

namespace E213.Lib.Math.Diagonal.Irrelevance

open E213.Theory E213.Lens

/-- Two Lenses agree on base and off-diagonal combine. -/
def OffDiagonalAgree {α : Type} (L L' : Lens α) : Prop :=
  L.base_a = L'.base_a ∧ L.base_b = L'.base_b ∧
  (∀ u v : α, u ≠ v → L.combine u v = L'.combine u v)

/-- **Diagonal irrelevance** — for an injective Lens, the diagonal
    value of combine has no effect on view.  If L and L' agree
    off-diagonally and combine is symmetric, their views agree on all
    of Raw. -/
theorem diagonal_irrelevant {α : Type} (L L' : Lens α)
    (hinj : Function.Injective L.view)
    (hLsym  : ∀ u v : α, L.combine  u v = L.combine  v u)
    (hL'sym : ∀ u v : α, L'.combine u v = L'.combine v u)
    (hagree : OffDiagonalAgree L L') :
    ∀ r : Raw, L.view r = L'.view r := by
  obtain ⟨hba, hbb, hcomb⟩ := hagree
  intro r
  induction r using Raw.rec with
  | a =>
      show L.base_a = L'.base_a
      exact hba
  | b =>
      show L.base_b = L'.base_b
      exact hbb
  | slash x y h ihx ihy =>
      have hfsL : L.view (Raw.slash x y h)
                    = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash L.base_a L.base_b L.combine hLsym x y h
      have hfsL' : L'.view (Raw.slash x y h)
                    = L'.combine (L'.view x) (L'.view y) :=
        Raw.fold_slash L'.base_a L'.base_b L'.combine hL'sym x y h
      rw [hfsL, hfsL', ← ihx, ← ihy]
      apply hcomb
      intro heq
      exact h (hinj heq)

/-- **Diagonal visibility** — if there is a view-collision, the diagonal
    value appears directly in view.  That is, changing `L.combine v v`
    changes `L.view (slash x y h)` when x, y are a v-collision pair. -/
theorem diagonal_reached_of_collision {α : Type} (L : Lens α)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x y : Raw) (h : x ≠ y) (hcol : L.view x = L.view y) :
    L.view (Raw.slash x y h) = L.combine (L.view x) (L.view x) := by
  have hfs : L.view (Raw.slash x y h)
               = L.combine (L.view x) (L.view y) :=
    Raw.fold_slash L.base_a L.base_b L.combine hLsym x y h
  rw [hfs, ← hcol]

end E213.Lib.Math.Diagonal.Irrelevance
