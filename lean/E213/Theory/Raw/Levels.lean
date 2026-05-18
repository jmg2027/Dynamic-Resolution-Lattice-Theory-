import E213.Term.Tree
import E213.Theory.Raw.Swap
import E213.Theory.Raw.Fold

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
