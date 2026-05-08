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
      have hcan := h
      unfold Tree.canonical at hcan
      obtain ⟨hxy_can, _⟩ := Bool.and_eq_true_to_pair hcan
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy_can
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      show (match Tree.cmp (Tree.swap x) (Tree.swap y) with
            | .lt => Tree.slash (Tree.swap x) (Tree.swap y)
            | .gt => Tree.slash (Tree.swap y) (Tree.swap x)
            | .eq => Tree.swap x).depth
            = (Tree.slash x y).depth
      split <;> rename_i hcmp
      · show 1 + max (Tree.swap x).depth (Tree.swap y).depth
             = 1 + max x.depth y.depth
        rw [ihx', ihy']
      · show 1 + max (Tree.swap y).depth (Tree.swap x).depth
             = 1 + max x.depth y.depth
        rw [ihx', ihy']
        exact congrArg (1 + ·) (Nat213.max_comm y.depth x.depth)
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
      have hcan := h
      unfold Tree.canonical at hcan
      obtain ⟨hxy_can, _⟩ := Bool.and_eq_true_to_pair hcan
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy_can
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      show (match Tree.cmp (Tree.swap x) (Tree.swap y) with
            | .lt => Tree.slash (Tree.swap x) (Tree.swap y)
            | .gt => Tree.slash (Tree.swap y) (Tree.swap x)
            | .eq => Tree.swap x).leaves
            = (Tree.slash x y).leaves
      split <;> rename_i hcmp
      · show (Tree.swap x).leaves + (Tree.swap y).leaves
             = x.leaves + y.leaves
        rw [ihx', ihy']
      · show (Tree.swap y).leaves + (Tree.swap x).leaves
             = x.leaves + y.leaves
        rw [ihx', ihy', Nat.add_comm]
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
