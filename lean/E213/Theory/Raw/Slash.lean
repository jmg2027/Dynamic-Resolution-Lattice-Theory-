import E213.Theory.Raw.Core
import E213.Term.Tree

/-!
# Theory.Raw.Slash: the `slash` smart constructor + `depth`

Raw.slash canonicalises the child order using `Tree.cmp`;
Raw.slash_comm reflects the axiom's directionless "between".
Tree.depth is the basic structural observable.
-/

namespace E213.Theory

open E213.Term.Internal

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

end E213.Theory

namespace E213.Term.Internal
def Tree.depth : Tree → Nat
  | .a         => 0
  | .b         => 0
  | .slash x y => 1 + max x.depth y.depth
end E213.Term.Internal

namespace E213.Theory

protected def Raw.depth (r : Raw) : Nat := r.val.depth

example : Raw.depth Raw.a = 0 := rfl
example : Raw.depth Raw.b = 0 := rfl

end E213.Theory
