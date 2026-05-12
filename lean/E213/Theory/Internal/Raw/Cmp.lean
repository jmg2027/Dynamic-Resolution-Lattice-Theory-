import E213.Theory.Raw.Core

/-!
# Theory.Internal.Raw.Cmp: lexicographic lemmas on `Tree.cmp`
+ ∅-axiom Bool / Nat helpers (`Bool.and_eq_true_to_pair`,
`Nat213.max_comm`) used by Slash / Swap / Rec / Levels.

Three support lemmas in `E213.Theory.Internal`, used by
`Slash`, `Swap`, and `Rec` sub-modules.
-/

namespace E213.Theory.Internal

theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a =>
      cases y with
      | a => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | b => exact ⟨fun h => Ordering.noConfusion h, fun h => Tree.noConfusion h⟩
      | slash _ _ => exact ⟨fun h => Ordering.noConfusion h, fun h => Tree.noConfusion h⟩
  | b =>
      cases y with
      | a => exact ⟨fun h => Ordering.noConfusion h, fun h => Tree.noConfusion h⟩
      | b => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | slash _ _ => exact ⟨fun h => Ordering.noConfusion h, fun h => Tree.noConfusion h⟩
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => exact ⟨fun h => Ordering.noConfusion h, fun h => Tree.noConfusion h⟩
      | b => exact ⟨fun h => Ordering.noConfusion h, fun h => Tree.noConfusion h⟩
      | slash x₂ y₂ =>
          show (match Tree.cmp x₁ x₂ with
                | .eq => Tree.cmp y₁ y₂
                | .lt => .lt
                | .gt => .gt) = .eq ↔ _
          constructor
          · intro h
            split at h <;> rename_i hc
            · have hx : x₁ = x₂ := (ihx x₂).mp hc
              have hy : y₁ = y₂ := (ihy y₂).mp h
              exact hx ▸ hy ▸ rfl
            · exact Ordering.noConfusion h
            · exact Ordering.noConfusion h
          · intro h
            injection h with hx hy
            have hcx : Tree.cmp x₁ x₂ = .eq := (ihx x₂).mpr hx
            have hcy : Tree.cmp y₁ y₂ = .eq := (ihy y₂).mpr hy
            rw [hcx]
            exact hcy

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

/-! ### One-direction (∅-axiom) versions of the iff lemmas

`cmp_eq_iff` and `cmp_gt_iff_lt_swap` use `simp` and bring `propext`.
These direct one-direction lemmas avoid both. -/

/-- Direct: `Tree.cmp x y = .eq → x = y` (no iff, no propext). -/
theorem Tree.cmp_eq_to_eq : ∀ (x y : Tree), Tree.cmp x y = .eq → x = y
  | .a, .a, _ => rfl
  | .a, .b, h => by cases h
  | .a, .slash _ _, h => by cases h
  | .b, .a, h => by cases h
  | .b, .b, _ => rfl
  | .b, .slash _ _, h => by cases h
  | .slash _ _, .a, h => by cases h
  | .slash _ _, .b, h => by cases h
  | .slash x₁ y₁, .slash x₂ y₂, h => by
      have h' : (match Tree.cmp x₁ x₂ with
                 | .eq => Tree.cmp y₁ y₂
                 | .lt => .lt
                 | .gt => .gt) = .eq := h
      cases hcx : Tree.cmp x₁ x₂ with
      | eq =>
          rw [hcx] at h'
          have hxe : x₁ = x₂ := Tree.cmp_eq_to_eq x₁ x₂ hcx
          have hye : y₁ = y₂ := Tree.cmp_eq_to_eq y₁ y₂ h'
          rw [hxe, hye]
      | lt => rw [hcx] at h'; cases h'
      | gt => rw [hcx] at h'; cases h'

/-- Direct: `Tree.cmp x x = .eq` (reflexivity, no iff). -/
theorem Tree.cmp_self_eq : ∀ (x : Tree), Tree.cmp x x = .eq
  | .a => rfl
  | .b => rfl
  | .slash x y => by
      show (match Tree.cmp x x with
            | .eq => Tree.cmp y y
            | .lt => .lt
            | .gt => .gt) = .eq
      rw [Tree.cmp_self_eq x]
      exact Tree.cmp_self_eq y

/-- Direct: `x = y → Tree.cmp x y = .eq` (no iff). -/
theorem Tree.cmp_eq_of_eq (x y : Tree) (h : x = y) : Tree.cmp x y = .eq :=
  h ▸ Tree.cmp_self_eq x

/-- Direct: `Tree.cmp x y = .gt → Tree.cmp y x = .lt` (no iff). -/
theorem Tree.cmp_gt_to_lt_swap (x y : Tree) (h : Tree.cmp x y = .gt) :
    Tree.cmp y x = .lt := by
  have hsw : Tree.cmp x y = (Tree.cmp y x).swap := Tree.cmp_swap x y
  rw [hsw] at h
  cases hyx : Tree.cmp y x with
  | lt => rfl
  | eq => rw [hyx] at h; cases h
  | gt => rw [hyx] at h; cases h

/-- Direct: `Tree.cmp x y = .lt → Tree.cmp y x = .gt` (no iff).
    Reverse direction of cmp_gt_to_lt_swap. -/
theorem Tree.cmp_lt_to_gt_swap (x y : Tree) (h : Tree.cmp x y = .lt) :
    Tree.cmp y x = .gt := by
  have hsw : Tree.cmp x y = (Tree.cmp y x).swap := Tree.cmp_swap x y
  rw [hsw] at h
  cases hyx : Tree.cmp y x with
  | lt => rw [hyx] at h; cases h
  | eq => rw [hyx] at h; cases h
  | gt => rfl

/-- ∅-axiom Bool destructor: `a && b = true → a = true ∧ b = true`. -/
theorem Bool.and_eq_true_to_pair : ∀ {a b : Bool},
    (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => by cases h
  | true, false, h => by cases h

/-- 213-native `Nat.max_comm` (Lean-core `Nat.max_comm` leaks
    `propext` via `Nat.max_eq_left`).  Used by `Tree.swap_depth`
    on the `.gt` branch where the swapped children appear in
    reverse order.  Pure: ∅-axiom. -/
theorem Nat213.max_comm (a b : Nat) : Nat.max a b = Nat.max b a := by
  show (if a ≤ b then b else a) = (if b ≤ a then a else b)
  rcases Nat.le_total a b with hab | hba
  · rw [if_pos hab]
    by_cases h : b ≤ a
    · rw [if_pos h]; exact Nat.le_antisymm h hab
    · rw [if_neg h]
  · rw [if_pos hba]
    by_cases h : a ≤ b
    · rw [if_pos h]; exact Nat.le_antisymm hba h
    · rw [if_neg h]

end E213.Theory.Internal
