import E213.Theory.Raw.Core
import E213.Term.Tree

/-!
# Theory.Raw.Slash: the Raw smart constructor `slash` + Raw.depth

`Raw.slash` canonicalises the child order using `Tree.cmp`;
`Raw.slash_comm` reflects the axiom's directionless "between".
`Raw.depth` is the basic structural observable (defined via
`Tree.depth` from Term.Internal.Tree.Levels).
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

-- ═══ Public API: smart constructor ═══

protected def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            unfold Tree.canonical
            rw [x.property, y.property, hc]; rfl⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              Tree.cmp_gt_to_lt_swap x.val y.val hc
            unfold Tree.canonical
            rw [y.property, x.property, hlt]; rfl⟩
  | .eq => absurd (Tree.cmp_eq_to_eq _ _ hc)
            (fun e => h (Subtype.ext e))

protected theorem Raw.slash_comm (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h = Raw.slash y x (Ne.symm h) := by
  unfold Raw.slash
  have hsw : Tree.cmp x.val y.val = (Tree.cmp y.val x.val).swap :=
    Tree.cmp_swap x.val y.val
  split <;> rename_i hc1 <;> split <;> rename_i hc2 <;>
    (first
      | rfl
      | (exfalso
         rw [hc1, hc2] at hsw
         cases hsw))

-- ═══ Public API: depth ═══

protected def Raw.depth (r : Raw) : Nat := r.val.depth

example : Raw.depth Raw.a = 0 := rfl
example : Raw.depth Raw.b = 0 := rfl

-- ═══ Public API: slash inequality ═══

/-- A canonical `Raw.slash x y h` is never equal to its right child.
    Follows from `Tree.leaves_pos`: the slash adds the leaves of `x`
    (≥ 1) to those of `y`, so the resulting tree has strictly more
    leaves than `y`. -/
protected theorem Raw.slash_ne_right (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ y := by
  intro heq
  have hval : (Raw.slash x y h).val = y.val := congrArg Subtype.val heq
  -- (Raw.slash x y h).val.leaves = x.val.leaves + y.val.leaves
  -- (by direct computation on the `match` branches of Raw.slash)
  have hsum : (Raw.slash x y h).val.leaves
              = x.val.leaves + y.val.leaves := by
    unfold Raw.slash
    split <;> rename_i hc
    · rfl
    · show y.val.leaves + x.val.leaves = x.val.leaves + y.val.leaves
      exact Nat.add_comm _ _
    · exfalso
      exact h (Subtype.ext (Tree.cmp_eq_to_eq _ _ hc))
  -- y.val.leaves = x.val.leaves + y.val.leaves (substitute hval into hsum)
  -- but x.val.leaves ≥ 1 contradicts this
  rw [hval] at hsum
  have hx_pos : 1 ≤ x.val.leaves := Tree.leaves_pos x.val
  have : y.val.leaves < x.val.leaves + y.val.leaves := by
    calc y.val.leaves
        < y.val.leaves + 1 := Nat.lt_succ_self _
      _ ≤ y.val.leaves + x.val.leaves :=
          Nat.add_le_add_left hx_pos _
      _ = x.val.leaves + y.val.leaves := Nat.add_comm _ _
  rw [← hsum] at this
  exact Nat.lt_irrefl _ this

end E213.Theory
