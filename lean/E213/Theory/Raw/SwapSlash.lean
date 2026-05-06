import E213.Theory.Raw.Swap
import E213.Theory.Raw.Slash

/-!
# Firmware.Raw.SwapSlash: compatibility of Raw.swap and Raw.slash

**Theorem**: `Raw.swap (Raw.slash x y h) = Raw.slash (swap x) (swap y) h'`.

Confirms that Raw.swap is an automorphism of Raw.  Case analysis on
canonical form.
-/

namespace E213.Theory

open E213.Theory.Internal

/-- **Raw.swap_slash**: compatibility of Raw.swap and Raw.slash. -/
theorem Raw.swap_slash (x y : Raw) (h : x ≠ y) :
    Raw.swap (Raw.slash x y h)
      = Raw.slash (Raw.swap x) (Raw.swap y)
          (fun e => h (Raw.swap_injective e)) := by
  apply Subtype.ext
  unfold Raw.slash Raw.swap
  split <;> rename_i hLcmp
  · -- cmp x.val y.val = .lt
    split <;> rename_i hRcmp
    · -- cmp (swap x.val) (swap y.val) = .lt
      show Tree.swap (.slash x.val y.val) = .slash (Tree.swap x.val) (Tree.swap y.val)
      simp only [Tree.swap, hRcmp]
    · -- cmp (swap x.val)(swap y.val) = .gt
      show Tree.swap (.slash x.val y.val) = .slash (Tree.swap y.val) (Tree.swap x.val)
      simp only [Tree.swap, hRcmp]
    · -- cmp (swap x.val)(swap y.val) = .eq: absurd via Tree.swap_eq_unreach
      exfalso
      exact Tree.swap_eq_unreach x.property y.property hLcmp hRcmp
  · -- cmp x.val y.val = .gt
    have hLlt : Tree.cmp y.val x.val = .lt :=
      (Tree.cmp_gt_iff_lt_swap _ _).mp hLcmp
    split <;> rename_i hRcmp
    · -- cmp (swap x)(swap y) = .lt
      -- Then cmp (swap y)(swap x) = .gt (by cmp_swap)
      show Tree.swap (.slash y.val x.val) = .slash (Tree.swap x.val) (Tree.swap y.val)
      have hRgt : Tree.cmp (Tree.swap y.val) (Tree.swap x.val) = .gt :=
        (Tree.cmp_gt_iff_lt_swap _ _).mpr hRcmp
      simp only [Tree.swap, hRgt]
    · -- cmp (swap x)(swap y) = .gt
      -- Then cmp (swap y)(swap x) = .lt
      show Tree.swap (.slash y.val x.val) = .slash (Tree.swap y.val) (Tree.swap x.val)
      have hRlt : Tree.cmp (Tree.swap y.val) (Tree.swap x.val) = .lt :=
        (Tree.cmp_gt_iff_lt_swap _ _).mp hRcmp
      simp only [Tree.swap, hRlt]
    · exfalso
      exact Tree.swap_eq_unreach y.property x.property hLlt
        (by rw [Tree.cmp_swap, hRcmp]; rfl)
  · -- cmp x.val y.val = .eq: absurd from h : x ≠ y
    exact absurd ((Tree.cmp_eq_iff _ _).mp hLcmp) (fun e => h (Subtype.ext e))

end E213.Theory
