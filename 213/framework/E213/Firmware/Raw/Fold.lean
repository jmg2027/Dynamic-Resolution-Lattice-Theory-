import E213.Firmware.Raw.Slash

/-!
# Firmware.Raw.Fold: catamorphism + compatibility with `slash`

The catamorphism `Raw.fold` is the unique homomorphism into
`(α, combine)` with given base values.  Lens implementations
are thin wrappers around this.  `Raw.fold_slash` ties the
homomorphism to the axiom's symmetric "between" when the
combine is symmetric.

Extracted from monolithic `Raw.lean` (Phase D).
-/

namespace E213.Firmware.Internal

def Tree.fold {α : Type}
    (fa fb : α) (fc : α → α → α) : Tree → α
  | .a         => fa
  | .b         => fb
  | .slash x y => fc (Tree.fold fa fb fc x) (Tree.fold fa fb fc y)

end E213.Firmware.Internal

namespace E213.Firmware

open E213.Firmware.Internal

/-- Catamorphism on Raw. -/
def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl

theorem Raw.fold_a {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.a = ba := rfl

theorem Raw.fold_b {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.b = bb := rfl

/-- Fold / slash compatibility for symmetric `combine`. -/
theorem Raw.fold_slash {α : Type}
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
  · exact absurd ((Tree.cmp_eq_iff _ _).mp hc) (fun e => h (Subtype.ext e))

end E213.Firmware
