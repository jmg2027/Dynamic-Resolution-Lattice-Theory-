import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold

/-!
# Firmware.Raw.Hom: general fold_swap_hom

For any `conj : α → α` that exchanges the base values and
distributes over a symmetric `combine`, `Raw.fold` on `Raw.swap`
equals `conj` applied to `Raw.fold`.  Consumers instantiate for
their own codomain (e.g., ℤ[i] with conj = complex conj).

Extracted from monolithic `Raw.lean` ().
-/

namespace E213.Theory.Internal

theorem Tree.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) :
    ∀ t : Tree, t.canonical = true →
    Tree.fold ba bb c (Tree.swap t) = conj (Tree.fold ba bb c t) := by
  intro t h
  induction t with
  | a => exact h_ba.symm
  | b => exact h_bb.symm
  | slash x y ihx ihy =>
      have hcan := h
      unfold Tree.canonical at hcan
      obtain ⟨hxy_can, _⟩ := Bool.and_eq_true_to_pair hcan
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy_can
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      show Tree.fold ba bb c
             (match Tree.cmp (Tree.swap x) (Tree.swap y) with
              | .lt => Tree.slash (Tree.swap x) (Tree.swap y)
              | .gt => Tree.slash (Tree.swap y) (Tree.swap x)
              | .eq => Tree.swap x)
           = conj (Tree.fold ba bb c (Tree.slash x y))
      split <;> rename_i hcmp_inner
      · show c (Tree.fold ba bb c (Tree.swap x)) (Tree.fold ba bb c (Tree.swap y))
             = conj (c (Tree.fold ba bb c x) (Tree.fold ba bb c y))
        rw [ihx', ihy', h_dist]
      · show c (Tree.fold ba bb c (Tree.swap y)) (Tree.fold ba bb c (Tree.swap x))
             = conj (c (Tree.fold ba bb c x) (Tree.fold ba bb c y))
        rw [ihx', ihy', h_dist, h_comm]
      · exact (Tree.swap_eq_unreach hx hy hlt hcmp_inner).elim

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

theorem Raw.fold_swap_hom {α : Type}
    (ba bb : α) (c : α → α → α) (conj : α → α)
    (h_ba : conj ba = bb) (h_bb : conj bb = ba)
    (h_dist : ∀ u v, conj (c u v) = c (conj u) (conj v))
    (h_comm : ∀ u v, c u v = c v u) (r : Raw) :
    Raw.fold ba bb c (Raw.swap r) = conj (Raw.fold ba bb c r) :=
  Tree.fold_swap_hom ba bb c conj h_ba h_bb h_dist h_comm r.val r.property

end E213.Theory
