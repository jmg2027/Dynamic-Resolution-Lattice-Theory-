import E213.Term.Tree
import E213.Theory.Raw.Slash

/-!
# Theory.Raw.Fold: Raw-level catamorphism + slash compatibility

Tree-level `fold` (def + recursion) lives in
`Term/Internal/Tree/Fold.lean`.  This file lifts it to `Raw` and
proves `fold_slash` — the homomorphism interaction with the
canonical smart constructor under symmetric `combine`.

**WARNING — axiom compliance (AXIOM.md §3)**: see Tree.fold note;
asymmetric `combine` makes the Lens silently leak the canonical
choice.  Every use of `Raw.fold` must verify symmetry.
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

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
