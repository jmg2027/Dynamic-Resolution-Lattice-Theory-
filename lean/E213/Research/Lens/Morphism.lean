import E213.Hypervisor.Lens

/-!
# Research.LensMorphism: morphism between Lens-algebras

A Lens is (base_a, base_b, combine) data over α.  A **morphism**
between two Lenses is a function preserving bases and combine:

```
IsLensMorphism h L M :=
  h L.base_a = M.base_a ∧
  h L.base_b = M.base_b ∧
  ∀ u v, h (L.combine u v) = M.combine (h u) (h v)
```

**Key theorem**: if h is an L-M morphism then `M.view = h ∘ L.view`.
That is, a Lens-morphism provides factoring at the view level.

While `refines_of_factor` from Note 39 is generic factoring, this
file is the stronger form of **factoring that preserves algebraic
structure**.
-/

namespace E213.Research.Lens.Morphism

open E213.Firmware E213.Hypervisor

/-- h is an L-M Lens morphism. -/
def IsLensMorphism {α β : Type} (h : α → β) (L : Lens α) (M : Lens β) :
    Prop :=
  h L.base_a = M.base_a ∧
  h L.base_b = M.base_b ∧
  ∀ u v : α, h (L.combine u v) = M.combine (h u) (h v)

/-- **Factoring through morphism**: if h is a Lens morphism then
    `M.view r = h (L.view r)` for all r. -/
theorem view_factors_through_morphism {α β : Type}
    (L : Lens α) (M : Lens β) (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) :
    ∀ r : Raw, M.view r = h (L.view r) := by
  obtain ⟨hba, hbb, hcomb⟩ := hmor
  intro r
  induction r using Raw.rec with
  | a => show M.base_a = h L.base_a; exact hba.symm
  | b => show M.base_b = h L.base_b; exact hbb.symm
  | slash x y hxy ihx ihy =>
      have hfsM : M.view (Raw.slash x y hxy)
                    = M.combine (M.view x) (M.view y) :=
        Raw.fold_slash _ _ _ hMsym x y hxy
      have hfsL : L.view (Raw.slash x y hxy)
                    = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hLsym x y hxy
      rw [hfsM, hfsL, ihx, ihy, ← hcomb]

end E213.Research.Lens.Morphism

namespace E213.Research.Lens.Morphism

open E213.Firmware E213.Hypervisor

/-- **Morphism → Refinement**: if h is an L-M morphism then
    L.refines M (given symmetric combine). -/
theorem refines_of_morphism {α β : Type} (L : Lens α) (M : Lens β)
    (h : α → β)
    (hLsym : ∀ u v : α, L.combine u v = L.combine v u)
    (hMsym : ∀ u v : β, M.combine u v = M.combine v u)
    (hmor : IsLensMorphism h L M) : L.refines M := by
  intro x y hxy
  have hx : M.view x = h (L.view x) :=
    view_factors_through_morphism L M h hLsym hMsym hmor x
  have hy : M.view y = h (L.view y) :=
    view_factors_through_morphism L M h hLsym hMsym hmor y
  have hxy' : L.view x = L.view y := hxy
  show M.view x = M.view y
  rw [hx, hy, hxy']

end E213.Research.Lens.Morphism
