import E213.Research.LensLattice
import E213.Prelude

/-!
# Research.LensMeet: meet (greatest lower bound) of the refines preorder

Answer to note 37 Q37.1.

The **meet** (coarsest common refinement) of two Lenses
`L : Lens α` and `M : Lens β` is their product:

```
prodLens L M : Lens (α × β)
```

The view is the pair `(L.view r, M.view r)` and the kernel is
`L.ker ∩ M.ker`.

- `prod_view` — view is the pair.
- `prod_refines_fst/snd` — product refines both sides.
- `prod_is_meet` — universal property (greatest lower bound).
-/

namespace E213.Research.LensMeet

open E213.Firmware E213.Hypervisor

/-- Product Lens: componentwise data. -/
def prodLens {α β : Type} (L : Lens α) (M : Lens β) : Lens (α × β) where
  base_a := (L.base_a, M.base_a)
  base_b := (L.base_b, M.base_b)
  combine p q := (L.combine p.1 q.1, M.combine p.2 q.2)

theorem prodLens_view {α β : Type} (L : Lens α) (M : Lens β)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (r : Raw) : (prodLens L M).view r = (L.view r, M.view r) := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hsym_prod : ∀ u v : α × β,
          (prodLens L M).combine u v = (prodLens L M).combine v u := by
        intro u v
        show (L.combine u.1 v.1, M.combine u.2 v.2)
           = (L.combine v.1 u.1, M.combine v.2 u.2)
        rw [hLsym, hMsym]
      have hfsP : (prodLens L M).view (Raw.slash x y h)
                    = (prodLens L M).combine ((prodLens L M).view x) ((prodLens L M).view y) :=
        Raw.fold_slash _ _ _ hsym_prod x y h
      have hfsL : L.view (Raw.slash x y h)
                    = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hLsym x y h
      have hfsM : M.view (Raw.slash x y h)
                    = M.combine (M.view x) (M.view y) :=
        Raw.fold_slash _ _ _ hMsym x y h
      rw [hfsP, hfsL, hfsM, ihx, ihy]
      rfl

end E213.Research.LensMeet

namespace E213.Research.LensMeet

open E213.Firmware E213.Hypervisor

/-- the product refines the left Lens. -/
theorem prodLens_refines_fst {α β : Type} (L : Lens α) (M : Lens β)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hMsym : ∀ u v, M.combine u v = M.combine v u) :
    (prodLens L M).refines L := by
  intro x y hxy
  have hx := prodLens_view L M hLsym hMsym x
  have hy := prodLens_view L M hLsym hMsym y
  show L.view x = L.view y
  have hp : (L.view x, M.view x) = (L.view y, M.view y) := by
    rw [← hx, ← hy]; exact hxy
  exact congrArg Prod.fst hp

/-- the product refines the right Lens. -/
theorem prodLens_refines_snd {α β : Type} (L : Lens α) (M : Lens β)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hMsym : ∀ u v, M.combine u v = M.combine v u) :
    (prodLens L M).refines M := by
  intro x y hxy
  have hx := prodLens_view L M hLsym hMsym x
  have hy := prodLens_view L M hLsym hMsym y
  show M.view x = M.view y
  have hp : (L.view x, M.view x) = (L.view y, M.view y) := by
    rw [← hx, ← hy]; exact hxy
  exact congrArg Prod.snd hp

end E213.Research.LensMeet

namespace E213.Research.LensMeet

open E213.Firmware E213.Hypervisor

/-- **Meet universal property**: if N refines both L and M, then N
    also refines their product.  Hence prodLens L M is the greatest
    lower bound of L and M in the refines preorder. -/
theorem prodLens_is_meet {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (hNL : N.refines L) (hNM : N.refines M) :
    N.refines (prodLens L M) := by
  intro x y hxy
  show (prodLens L M).view x = (prodLens L M).view y
  rw [prodLens_view L M hLsym hMsym, prodLens_view L M hLsym hMsym]
  have hL : L.view x = L.view y := hNL x y hxy
  have hM : M.view x = M.view y := hNM x y hxy
  rw [hL, hM]

end E213.Research.LensMeet
