import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold

/-!
# Firmware.Raw.Levels: swap-depth / swap-leaves invariance
+ fold-bridges into depth / leaves observables.

Extracted from monolithic `Raw.lean` ().
-/

namespace E213.Theory.Internal

theorem Tree.swap_depth :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).depth = t.depth := by
  intro t h
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp
      · simp only [Tree.depth, ihx', ihy']
      · simp only [Tree.depth, ihx', ihy', Nat.max_comm]
      · exact (Tree.swap_eq_unreach hx hy hlt hcmp).elim

def Tree.leaves : Tree → Nat
  | .a         => 1
  | .b         => 1
  | .slash x y => x.leaves + y.leaves

theorem Tree.swap_leaves :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).leaves = t.leaves := by
  intro t h
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp
      · simp only [Tree.leaves, ihx', ihy']
      · simp only [Tree.leaves, ihx', ihy', Nat.add_comm]
      · exact (Tree.swap_eq_unreach hx hy hlt hcmp).elim

end E213.Theory.Internal

namespace E213.Theory.Internal

theorem Tree.fold_eq_depth : ∀ t : Tree,
    Tree.fold 0 0 (fun a b => 1 + max a b) t = t.depth := by
  intro t
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show (1 + max (Tree.fold 0 0 _ x) (Tree.fold 0 0 _ y))
           = 1 + max x.depth y.depth
      rw [ihx, ihy]

theorem Tree.fold_eq_leaves : ∀ t : Tree,
    Tree.fold 1 1 (· + ·) t = t.leaves := by
  intro t
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show (Tree.fold 1 1 _ x + Tree.fold 1 1 _ y) = x.leaves + y.leaves
      rw [ihx, ihy]

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property

def Raw.leaves (r : Raw) : Nat := r.val.leaves

theorem Raw.swap_leaves (r : Raw) : (Raw.swap r).leaves = r.leaves :=
  Tree.swap_leaves r.val r.property

theorem Raw.fold_eq_depth (r : Raw) :
    Raw.fold 0 0 (fun a b => 1 + max a b) r = r.depth :=
  Tree.fold_eq_depth r.val

theorem Raw.fold_eq_leaves (r : Raw) :
    Raw.fold 1 1 (· + ·) r = r.leaves :=
  Tree.fold_eq_leaves r.val

end E213.Theory
