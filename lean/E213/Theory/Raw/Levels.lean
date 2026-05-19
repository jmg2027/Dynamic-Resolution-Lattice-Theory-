import E213.Term.Tree
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold
import E213.Theory.Raw.Rec
import E213.Meta.Tactic.NatHelper

/-!
# Theory.Raw.Levels: Raw-level swap-depth / swap-leaves invariance
+ fold-bridges into depth / leaves observables, + explicit level-≤2
enumeration.

Tree-level definitions and lemmas (Tree.depth, Tree.leaves,
Tree.swap_depth, Tree.swap_leaves, Tree.fold_eq_depth,
Tree.fold_eq_leaves) live in `Term/Internal/Tree/Levels.lean`.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

protected theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property

protected def Raw.leaves (r : Raw) : Nat := r.val.leaves

protected theorem Raw.swap_leaves (r : Raw) : (Raw.swap r).leaves = r.leaves :=
  Tree.swap_leaves r.val r.property

protected theorem Raw.fold_eq_depth (r : Raw) :
    Raw.fold 0 0 (fun a b => 1 + max a b) r = r.depth :=
  Tree.fold_eq_depth r.val

protected theorem Raw.fold_eq_leaves (r : Raw) :
    Raw.fold 1 1 (· + ·) r = r.leaves :=
  Tree.fold_eq_leaves r.val

/-- `Raw.leaves r ≥ 1` for every Raw — every Tree has at least one
    leaf.  Direct from `Tree.leaves_pos`. -/
protected theorem Raw.leaves_pos (r : Raw) : 1 ≤ r.leaves :=
  Tree.leaves_pos r.val

/-- `(Raw.slash x y h).depth = 1 + max x.depth y.depth`.  Depth
    recursion at the Raw level — uses `fold_eq_depth` to route
    through the catamorphism, then `fold_slash` with the
    propext-free `NatHelper.max_comm_pure`. -/
protected theorem Raw.depth_slash (x y : Raw) (h : x ≠ y) :
    (Raw.slash x y h).depth = 1 + max x.depth y.depth := by
  rw [← Raw.fold_eq_depth, ← Raw.fold_eq_depth x, ← Raw.fold_eq_depth y]
  have hsym : ∀ u v : Nat, 1 + max u v = 1 + max v u :=
    fun u v => congrArg (1 + ·) (E213.Tactic.NatHelper.max_comm_pure u v)
  exact Raw.fold_slash 0 0 (fun a b => 1 + max a b) hsym x y h

/-- `(Raw.slash x y h).leaves = x.leaves + y.leaves`.  Leaves
    recursion at the Raw level — direct from `fold_eq_leaves` +
    `fold_slash` with `Nat.add_comm`. -/
protected theorem Raw.leaves_slash (x y : Raw) (h : x ≠ y) :
    (Raw.slash x y h).leaves = x.leaves + y.leaves := by
  rw [← Raw.fold_eq_leaves, ← Raw.fold_eq_leaves x, ← Raw.fold_eq_leaves y]
  exact Raw.fold_slash 1 1 (· + ·) Nat.add_comm x y h

/-- A `slash` Raw always has depth ≥ 1.  Direct corollary of
    `depth_slash`. -/
protected theorem Raw.depth_slash_pos (x y : Raw) (h : x ≠ y) :
    1 ≤ (Raw.slash x y h).depth := by
  rw [Raw.depth_slash x y h]
  exact Nat.le_add_right 1 _

/-- **Universal binary-tree inequality**: `depth r < leaves r`
    for every Raw.  Equivalently, `r.leaves ≥ r.depth + 1`.
    Standard binary-tree fact: at each slash node, the deeper
    branch contributes ≥ depth+1 leaves; the other branch
    contributes ≥ 1 more.  Proven by `Raw.rec` induction. -/
protected theorem Raw.depth_lt_leaves (r : Raw) : r.depth < r.leaves := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      rw [Raw.depth_slash x y h, Raw.leaves_slash x y h]
      have hxd : x.depth + 1 ≤ x.leaves := ihx
      have hyd : y.depth + 1 ≤ y.leaves := ihy
      have hxp : 1 ≤ x.leaves := Raw.leaves_pos x
      have hyp : 1 ≤ y.leaves := Raw.leaves_pos y
      show 1 + max x.depth y.depth + 1 ≤ x.leaves + y.leaves
      cases Nat.lt_or_ge y.depth x.depth with
      | inl hlt =>
          have hmax : max x.depth y.depth = x.depth :=
            E213.Tactic.NatHelper.max_eq_left_pure (Nat.le_of_lt hlt)
          rw [hmax]
          calc 1 + x.depth + 1
              = (x.depth + 1) + 1 := by rw [Nat.add_comm 1 x.depth]
            _ ≤ x.leaves + 1 := Nat.add_le_add_right hxd 1
            _ ≤ x.leaves + y.leaves := Nat.add_le_add_left hyp _
      | inr hge =>
          have hmax : max x.depth y.depth = y.depth :=
            (E213.Tactic.NatHelper.max_comm_pure x.depth y.depth).trans
              (E213.Tactic.NatHelper.max_eq_left_pure hge)
          rw [hmax]
          calc 1 + y.depth + 1
              = (y.depth + 1) + 1 := by rw [Nat.add_comm 1 y.depth]
            _ ≤ y.leaves + 1 := Nat.add_le_add_right hyd 1
            _ ≤ y.leaves + x.leaves := Nat.add_le_add_left hxp _
            _ = x.leaves + y.leaves := Nat.add_comm _ _

/-- Reformulation of `depth_lt_leaves`: `r.depth + 1 ≤ r.leaves`. -/
protected theorem Raw.leaves_ge_depth_succ (r : Raw) :
    r.depth + 1 ≤ r.leaves :=
  Raw.depth_lt_leaves r

/-- Corollary: a Raw with depth ≥ 1 has at least 2 leaves. -/
protected theorem Raw.leaves_ge_two_of_depth_pos (r : Raw)
    (h : 1 ≤ r.depth) : 2 ≤ r.leaves := by
  have h1 : r.depth + 1 ≤ r.leaves := Raw.depth_lt_leaves r
  have h2 : 2 ≤ r.depth + 1 := Nat.add_le_add_right h 1
  exact Nat.le_trans h2 h1

-- ═══ Explicit level-≤2 enumeration ═══
-- (Backing §1.3 and §5.1 of the paper.  Uses only the public
--  `Raw.slash` API — no Tree internals.)

/-- Level-≤1 witnesses: the Raw terms `a`, `b`, `a/b`
    (a `List Raw`, not a ZFC set; order is the enumeration
    Lens choice, not axiomatic). -/
protected def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions: the Raw terms `a/(a/b)`, `b/(a/b)`. -/
protected def Raw.level2_new : List Raw :=
  [Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide),
   Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide)]

protected theorem Raw.level1_card : Raw.level1_set.length = 3 := rfl
protected theorem Raw.level2_new_card : Raw.level2_new.length = 2 := rfl
protected theorem Raw.level2_total_card :
    (Raw.level1_set ++ Raw.level2_new).length = 5 := rfl

example : (Raw.level1_set ++ Raw.level2_new).Nodup := by decide

end E213.Theory
