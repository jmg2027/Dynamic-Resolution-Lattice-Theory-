import E213.Firmware.Raw.Core

/-!
# Firmware.Raw.Cmp: lexicographic lemmas on `Tree.cmp`

Three support lemmas in `E213.Firmware.Internal`, used by
`Slash`, `Swap`, and `Rec` sub-modules.

Extracted from monolithic `Raw.lean` (Phase D).
-/

namespace E213.Firmware.Internal

theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a => cases y <;> simp [Tree.cmp]
  | b => cases y <;> simp [Tree.cmp]
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => simp [Tree.cmp]
      | b => simp [Tree.cmp]
      | slash x₂ y₂ =>
          simp only [Tree.cmp]
          constructor
          · intro h
            split at h <;> rename_i hc
            · rw [(ihy y₂).mp h, show x₁ = x₂ from (ihx x₂).mp hc]
            all_goals cases h
          · intro h
            injection h with hx hy
            rw [← hx, ← hy]
            rw [show Tree.cmp x₁ x₁ = .eq from (ihx x₁).mpr rfl]
            exact (ihy y₁).mpr rfl

theorem Tree.cmp_swap (x y : Tree) :
    Tree.cmp x y = (Tree.cmp y x).swap := by
  induction x generalizing y with
  | a => cases y <;> rfl
  | b => cases y <;> rfl
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => rfl
      | b => rfl
      | slash x₂ y₂ =>
          show (match Tree.cmp x₁ x₂ with
                | .eq => Tree.cmp y₁ y₂
                | .lt => .lt
                | .gt => .gt)
              = (match Tree.cmp x₂ x₁ with
                 | .eq => Tree.cmp y₂ y₁
                 | .lt => .lt
                 | .gt => .gt).swap
          rw [ihx x₂, ihy y₂]
          cases Tree.cmp x₂ x₁ <;> rfl

theorem Tree.cmp_gt_iff_lt_swap (x y : Tree) :
    Tree.cmp x y = .gt ↔ Tree.cmp y x = .lt := by
  rw [Tree.cmp_swap x y]
  cases Tree.cmp y x <;> simp [Ordering.swap]

end E213.Firmware.Internal
