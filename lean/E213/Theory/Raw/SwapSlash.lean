import E213.Theory.Raw.Swap
import E213.Theory.Raw.Slash

/-!
# Theory.Raw.SwapSlash: compatibility of Raw.swap and Raw.slash

**Theorem**: `Raw.swap (Raw.slash x y h) = Raw.slash (swap x) (swap y) h'`.

Confirms that Raw.swap is an automorphism of Raw.  Case analysis on
canonical form.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

/-- **Raw.swap_slash**: compatibility of Raw.swap and Raw.slash. -/
protected theorem Raw.swap_slash (x y : Raw) (h : x ≠ y) :
    Raw.swap (Raw.slash x y h)
      = Raw.slash (Raw.swap x) (Raw.swap y)
          (fun e => h (Raw.swap_injective e)) := by
  apply Subtype.ext
  unfold Raw.slash Raw.swap
  split <;> rename_i hLcmp
  · -- cmp x.val y.val = .lt
    split <;> rename_i hRcmp
    · -- cmp (swap x.val) (swap y.val) = .lt
      show Tree.swap (Tree.slash x.val y.val)
           = Tree.slash (Tree.swap x.val) (Tree.swap y.val)
      show (match Tree.cmp (Tree.swap x.val) (Tree.swap y.val) with
            | .lt => Tree.slash (Tree.swap x.val) (Tree.swap y.val)
            | .gt => Tree.slash (Tree.swap y.val) (Tree.swap x.val)
            | .eq => Tree.swap x.val)
           = Tree.slash (Tree.swap x.val) (Tree.swap y.val)
      rw [hRcmp]
    · -- cmp (swap x.val)(swap y.val) = .gt
      show Tree.swap (Tree.slash x.val y.val)
           = Tree.slash (Tree.swap y.val) (Tree.swap x.val)
      show (match Tree.cmp (Tree.swap x.val) (Tree.swap y.val) with
            | .lt => Tree.slash (Tree.swap x.val) (Tree.swap y.val)
            | .gt => Tree.slash (Tree.swap y.val) (Tree.swap x.val)
            | .eq => Tree.swap x.val)
           = Tree.slash (Tree.swap y.val) (Tree.swap x.val)
      rw [hRcmp]
    · -- cmp (swap x.val)(swap y.val) = .eq: absurd via Tree.swap_eq_unreach
      exfalso
      exact Tree.swap_eq_unreach x.property y.property hLcmp hRcmp
  · -- cmp x.val y.val = .gt
    have hLlt : Tree.cmp y.val x.val = .lt :=
      Tree.cmp_gt_to_lt_swap _ _ hLcmp
    split <;> rename_i hRcmp
    · -- cmp (swap x)(swap y) = .lt
      -- Then cmp (swap y)(swap x) = .gt (by cmp_swap)
      show Tree.swap (Tree.slash y.val x.val)
           = Tree.slash (Tree.swap x.val) (Tree.swap y.val)
      have hRgt : Tree.cmp (Tree.swap y.val) (Tree.swap x.val) = .gt :=
        Tree.cmp_lt_to_gt_swap _ _ hRcmp
      show (match Tree.cmp (Tree.swap y.val) (Tree.swap x.val) with
            | .lt => Tree.slash (Tree.swap y.val) (Tree.swap x.val)
            | .gt => Tree.slash (Tree.swap x.val) (Tree.swap y.val)
            | .eq => Tree.swap y.val)
           = Tree.slash (Tree.swap x.val) (Tree.swap y.val)
      rw [hRgt]
    · -- cmp (swap x)(swap y) = .gt
      -- Then cmp (swap y)(swap x) = .lt
      show Tree.swap (Tree.slash y.val x.val)
           = Tree.slash (Tree.swap y.val) (Tree.swap x.val)
      have hRlt : Tree.cmp (Tree.swap y.val) (Tree.swap x.val) = .lt :=
        Tree.cmp_gt_to_lt_swap _ _ hRcmp
      show (match Tree.cmp (Tree.swap y.val) (Tree.swap x.val) with
            | .lt => Tree.slash (Tree.swap y.val) (Tree.swap x.val)
            | .gt => Tree.slash (Tree.swap x.val) (Tree.swap y.val)
            | .eq => Tree.swap y.val)
           = Tree.slash (Tree.swap y.val) (Tree.swap x.val)
      rw [hRlt]
    · exfalso
      exact Tree.swap_eq_unreach y.property x.property hLlt
        (by rw [Tree.cmp_swap, hRcmp]; rfl)
  · -- cmp x.val y.val = .eq: absurd from h : x ≠ y
    exact absurd (Tree.cmp_eq_to_eq _ _ hLcmp) (fun e => h (Subtype.ext e))

end E213.Theory
