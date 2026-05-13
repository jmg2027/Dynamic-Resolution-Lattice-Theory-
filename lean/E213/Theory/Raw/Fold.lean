import E213.Theory.Raw.Slash

/-!
# Theory.Raw.Fold: catamorphism + compatibility with `slash`

The catamorphism `Raw.fold` is the unique homomorphism into
`(α, combine)` with given base values.  Lens implementations
are thin wrappers around this.  `Raw.fold_slash` ties the
homomorphism to the axiom's symmetric "between" when the
combine is symmetric.

**WARNING — axiom compliance (AXIOM.md §3)**: `Raw.fold` does not
require symmetry of `combine` at the type level.  However, using an
asymmetric `combine` makes the result depend on the Tree's canonical
ordering (= an encoding artifact, not an axiom).  Such a Lens is a
**silent leak** violating the axiom.  Every use of `Raw.fold` must
verify that `combine` is symmetric (∀ u v, combine u v = combine v u).
The `fold_slash` theorem already documents this symmetry assumption.
-/

namespace E213.Theory.Internal

def Tree.fold {α : Type}
    (fa fb : α) (fc : α → α → α) : Tree → α
  | .a         => fa
  | .b         => fb
  | .slash x y => fc (Tree.fold fa fb fc x) (Tree.fold fa fb fc y)

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

/-- Catamorphism on Raw. -/
protected def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl

protected theorem Raw.fold_a {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.a = ba := rfl

protected theorem Raw.fold_b {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.b = bb := rfl

/-- Fold / slash compatibility for symmetric `combine`. -/
protected theorem Raw.fold_slash {α : Type}
    (ba bb : α) (c : α → α → α)
    (hsym : ∀ u v : α, c u v = c v u)
    (x y : Raw) (h : x ≠ y) :
    Raw.fold ba bb c (Raw.slash x y h)
      = c (Raw.fold ba bb c x) (Raw.fold ba bb c y) := by
  unfold Raw.slash Raw.fold
  split <;> rename_i hc
  · show c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val)
         = c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val)
    rfl
  · show c (Tree.fold ba bb c y.val) (Tree.fold ba bb c x.val)
         = c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val)
    exact hsym _ _
  · exact absurd (Tree.cmp_eq_to_eq _ _ hc) (fun e => h (Subtype.ext e))

end E213.Theory
