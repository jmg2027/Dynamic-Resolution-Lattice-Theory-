import E213.Hypervisor.Lens
import E213.Prelude

/-!
# Research.DiagonalIrrelevance: Lens combine 의 diagonal 거동

Note 34 §3-§4 의 Lean 화.

## 주장

- **injective Lens**: `Function.Injective L.view` 이면 `L.combine` 의
  diagonal 값은 view 에 영향 없음 (`diagonal_irrelevant`).
  off-diagonal 값만 같으면 두 Lens 의 view 가 Raw 전체에서 일치.
- **non-injective Lens**: view-collision (`∃ x ≠ y, view x = view y`)
  이 있으면 diagonal 값이 `view (slash x y h)` 에서 직접 hit
  (`diagonal_reached_of_collision`).

Note 34 §4 원문 ("PartialLens.view 는 Raw 수준 diagonal 미접촉")
은 부정확.  diagonal hit 은 view 단사성에 의해 결정됨.
-/

namespace E213.Research.DiagonalIrrelevance

open E213.Firmware E213.Hypervisor

/-- 두 Lens 가 base 와 off-diagonal combine 에서 일치. -/
def OffDiagonalAgree {α : Type} (L L' : Lens α) : Prop :=
  L.base_a = L'.base_a ∧ L.base_b = L'.base_b ∧
  (∀ u v : α, u ≠ v → L.combine u v = L'.combine u v)

/-- **Diagonal irrelevance** — injective Lens 에서는 combine 의
    diagonal 값이 view 에 영향 없음.  L, L' 가 off-diagonal
    일치하고 combine 이 대칭이면 view 는 Raw 전체에서 같음. -/
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

/-- **Diagonal 가시성** — view-collision 이 있으면 diagonal
    값이 view 에 직접 나타남.  즉 `L.combine v v` 를 바꾸면
    `L.view (slash x y h)` 가 바뀐다 (x, y 가 v-collision 쌍). -/
theorem diagonal_reached_of_collision {α : Type} (L : Lens α)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x y : Raw) (h : x ≠ y) (hcol : L.view x = L.view y) :
    L.view (Raw.slash x y h) = L.combine (L.view x) (L.view x) := by
  have hfs : L.view (Raw.slash x y h)
               = L.combine (L.view x) (L.view y) :=
    Raw.fold_slash L.base_a L.base_b L.combine hLsym x y h
  rw [hfs, ← hcol]

end E213.Research.DiagonalIrrelevance
