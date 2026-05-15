import E213.Theory.Raw.API

/-!
# Lens ring

Each `Lens` supplies a codomain `α` with two base values and a
binary op. `Lens.view` is the catamorphism `Raw → α`, implemented
as a wrapper around the firmware's `Raw.fold`.

The Lens's kernel `L.equiv x y := L.view x = L.view y` supplies
the first notion of equality on `Raw`. Different Lenses impose
different equalities; none is part of the axiom.

**This module uses only the Theory's public API (Theory.Raw)** (`Raw`,
`Raw.a`, `Raw.b`, `Raw.slash`, `Raw.fold`, `Raw.slash_comm`). The
internal `Tree` type and its ordering are not referenced.
-/

namespace E213.Lens

open E213.Theory

/-- A Lens: two base values + a binary op. -/
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

/-- The catamorphism. -/
protected def Lens.view {α : Type} (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine

-- Kernel equivalence: Lens-induced equality on Raw.
protected def Lens.equiv {α : Type} (L : Lens α) (x y : Raw) : Prop :=
  L.view x = L.view y

protected theorem Lens.equiv_refl {α} (L : Lens α) (x : Raw) : L.equiv x x := rfl

protected theorem Lens.equiv_symm {α} (L : Lens α) {x y : Raw} :
    L.equiv x y → L.equiv y x := Eq.symm

protected theorem Lens.equiv_trans {α} (L : Lens α) {x y z : Raw} :
    L.equiv x y → L.equiv y z → L.equiv x z := Eq.trans

-- Canonical Lenses.

/-- Leaves: counts base-object occurrences. -/
protected def Lens.leaves : Lens Nat := ⟨1, 1, (· + ·)⟩

/-- Depth: tree height. -/
protected def Lens.depth : Lens Nat := ⟨0, 0, fun a b => 1 + max a b⟩

-- Base-value computations (smoke tests).
example : Lens.leaves.view Raw.a = 1 := rfl
example : Lens.leaves.view Raw.b = 1 := rfl
example : Lens.depth.view Raw.a = 0 := rfl
example : Lens.depth.view Raw.b = 0 := rfl

-- Refines: L refines M iff L's kernel is finer than M's.
protected def Lens.refines {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y : Raw, L.equiv x y → M.equiv x y

protected theorem Lens.refines_refl {α} (L : Lens α) : L.refines L := fun _ _ h => h

protected theorem Lens.refines_trans {α β γ} {L : Lens α} {M : Lens β} {N : Lens γ} :
    L.refines M → M.refines N → L.refines N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

end E213.Lens
