import E213.Firmware.Raw.Core
import E213.Firmware.Raw.Cmp

/-!
# Firmware.Raw.Slash: the `slash` smart constructor + `depth`

Raw.slash canonicalises the child order using `Tree.cmp`;
Raw.slash_comm reflects the axiom's directionless "between".
Tree.depth is the basic structural observable.

Extracted from monolithic `Raw.lean` (Phase D).
-/

namespace E213.Firmware

open E213.Firmware.Internal

-- ═══ Public API: smart constructor ═══

def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            simp [Tree.canonical, x.property, y.property, hc]⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              (Tree.cmp_gt_iff_lt_swap x.val y.val).mp hc
            simp [Tree.canonical, y.property, x.property, hlt]⟩
  | .eq => absurd ((Tree.cmp_eq_iff _ _).mp hc)
            (fun e => h (Subtype.ext e))

theorem Raw.slash_comm (x y : Raw) (h : x ≠ y) :
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

namespace Internal
def Tree.depth : Tree → Nat
  | .a         => 0
  | .b         => 0
  | .slash x y => 1 + max x.depth y.depth
end Internal

def Raw.depth (r : Raw) : Nat := r.val.depth

example : Raw.depth Raw.a = 0 := rfl
example : Raw.depth Raw.b = 0 := rfl

end E213.Firmware
