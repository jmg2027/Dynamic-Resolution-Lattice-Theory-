import E213.Theory.Raw.API

/-!
# Lens ring

A `Lens α` supplies a codomain `α` with two base values and a
binary op.  `Lens.view` is the catamorphism `Raw → α`, implemented
as a wrapper around `Raw.fold` — Raw's fold instantiated in the
α algebra.  This is *Raw's self-reading recorded under the
α-Lens*, not an external observation acting on Raw (cf.
`seed/AXIOM/07_primacy.md` §7 + `07_self_reference.md` §8.1).

The Lens-induced kernel `L.equiv x y := L.view x = L.view y`
records α-view agreement on Raw — the equivalence Raw acquires
when its α-readings are compared.  Different Lenses induce
different kernels; none is part of the axiom.

**Module discipline**: only Theory's public API (`Raw`, `Raw.a`,
`Raw.b`, `Raw.slash`, `Raw.fold`, `Raw.slash_comm`) is used.  The
internal `Tree` type and its ordering are not referenced.
-/

namespace E213.Lens

open E213.Theory

/-- A Lens supplies the data that Raw's fold needs in codomain α:
    images for the two atomic constructors (base_a, base_b — the
    α-shadows of `Raw.a, Raw.b`) and a binary combine for slash.
    Per `seed/AXIOM/06_lens_readings.md` §6.1, "two" here is
    the count-Lens reading of Raw's first distinguishing (not a
    Raw cardinality claim); base_a, base_b are α-labels for one
    chart choice. -/
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

/-- The catamorphism: Raw's fold instantiated in α.  Not an
    external projection of Raw — `view` is the α-side recording
    of Raw's self-pointing (cf. §8.1 no exterior). -/
protected def Lens.view {α : Type} (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine

/-- α-view equivalence on Raw: two Raws agree in α iff they map
    to equal values.  This is Raw's α-shadow equivalence, not an
    external relation imposed on Raw. -/
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

/-- Every `Raw` has `Lens.leaves.view ≥ 1`.  The canonical leaves
    count is bounded below by 1 because both atoms count as 1
    and `slash` adds positive leaves. -/
protected theorem Lens.leaves_view_ge_one (r : Raw) :
    1 ≤ Lens.leaves.view r := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx _ =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]
      exact Nat.le_trans ihx (Nat.le_add_right _ _)

-- Refines: L refines M iff L's kernel is finer than M's.
protected def Lens.refines {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y : Raw, L.equiv x y → M.equiv x y

protected theorem Lens.refines_refl {α} (L : Lens α) : L.refines L := fun _ _ h => h

protected theorem Lens.refines_trans {α β γ} {L : Lens α} {M : Lens β} {N : Lens γ} :
    L.refines M → M.refines N → L.refines N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

end E213.Lens
