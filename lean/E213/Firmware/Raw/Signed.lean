import E213.Firmware.Raw.Swap
import E213.Firmware.Raw.Fold

/-!
# Firmware.Raw.Signed: fold_signed_swap — swap as negation

The signed Lens (base_a=1, base_b=-1, combine=+) realises swap
as integer negation.  Used by Hypervisor / App layers.

Extracted from monolithic `Raw.lean` ().
-/

namespace E213.Firmware.Internal

theorem Tree.fold_signed_swap :
    ∀ t : Tree, t.canonical = true →
    Tree.fold (1 : Int) (-1) (· + ·) (Tree.swap t)
      = - Tree.fold (1 : Int) (-1) (· + ·) t := by
  intro t h
  induction t with
  | a => decide
  | b => decide
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp_inner
      · show Tree.fold _ _ _ (Tree.swap x) + Tree.fold _ _ _ (Tree.swap y)
             = -(Tree.fold _ _ _ x + Tree.fold _ _ _ y)
        rw [ihx', ihy', Int.neg_add]
      · show Tree.fold _ _ _ (Tree.swap y) + Tree.fold _ _ _ (Tree.swap x)
             = -(Tree.fold _ _ _ x + Tree.fold _ _ _ y)
        rw [ihx', ihy', Int.neg_add, Int.add_comm]
      · exact (Tree.swap_eq_unreach hx hy hlt hcmp_inner).elim

end E213.Firmware.Internal

namespace E213.Firmware

open E213.Firmware.Internal

theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property

end E213.Firmware
