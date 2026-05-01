import E213.Hypervisor.Lens.Lattice.JoinEquiv
import E213.Hypervisor.Lens.Universal.QuotLens

/-!
# Research.JoinLens: concrete join Lens for an arbitrary Lens pair

`joinLens L M : Lens (Raw → Prop)` := `universalLens (JoinEquiv L M)`.

The combination of `JoinEquiv`'s universal property and
`universalLens_kernel_eq_E` yields a **concrete join Lens** for
every Lens pair.

Together with prodLens (meet), this completes the lattice structure
of the refines preorder.

## Key Theorems

- `joinLens_kernel`: kernel of joinLens L M = JoinEquiv L M.
- `L_refines_joinLens`, `M_refines_joinLens`: upper bound property.
- `joinLens_is_least`: least upper bound (universal property).
-/

namespace E213.Hypervisor.Lens.Lattice.Join

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Lattice.JoinEquiv E213.Hypervisor.Lens.Universal.QuotLens

/-- JoinEquiv L M is an equivalence relation. -/
private theorem joinEquiv_refl {α β : Type} (L : Lens α) (M : Lens β)
    (r : Raw) : JoinEquiv L M r r := JoinEquiv.refl r

private theorem joinEquiv_symm {α β : Type} (L : Lens α) (M : Lens β)
    (r r' : Raw) (h : JoinEquiv L M r r') : JoinEquiv L M r' r :=
  JoinEquiv.symm h

private theorem joinEquiv_trans {α β : Type} (L : Lens α) (M : Lens β)
    (r r' r'' : Raw)
    (h1 : JoinEquiv L M r r') (h2 : JoinEquiv L M r' r'') :
    JoinEquiv L M r r'' :=
  JoinEquiv.trans h1 h2

private theorem joinEquiv_slash {α β : Type} (L : Lens α) (M : Lens β)
    (x x' y y' : Raw) (h : x ≠ y) (h' : x' ≠ y')
    (hxx' : JoinEquiv L M x x') (hyy' : JoinEquiv L M y y') :
    JoinEquiv L M (Raw.slash x y h) (Raw.slash x' y' h') :=
  JoinEquiv.slash_cong h h' hxx' hyy'

/-- **Concrete join Lens**: join of an arbitrary Lens pair, made
    explicit via the universalLens construction. -/
def joinLens {α β : Type} (L : Lens α) (M : Lens β) : Lens (Raw → Prop) :=
  universalLens (JoinEquiv L M)

/-- **kernel = JoinEquiv**.  Direct consequence of universalLens. -/
theorem joinLens_kernel {α β : Type} (L : Lens α) (M : Lens β)
    (r r' : Raw) :
    (joinLens L M).view r = (joinLens L M).view r'
      ↔ JoinEquiv L M r r' := by
  apply universalLens_kernel_eq_E
  · exact joinEquiv_refl L M
  · exact joinEquiv_symm L M
  · exact joinEquiv_trans L M
  · exact joinEquiv_slash L M

/-- **L refines joinLens L M** (upper bound). -/
theorem L_refines_joinLens {α β : Type} (L : Lens α) (M : Lens β) :
    L.refines (joinLens L M) := by
  intro r r' h
  show (joinLens L M).view r = (joinLens L M).view r'
  rw [joinLens_kernel L M r r']
  exact JoinEquiv.ofL h

/-- **M refines joinLens L M** (upper bound). -/
theorem M_refines_joinLens {α β : Type} (L : Lens α) (M : Lens β) :
    M.refines (joinLens L M) := by
  intro r r' h
  show (joinLens L M).view r = (joinLens L M).view r'
  rw [joinLens_kernel L M r r']
  exact JoinEquiv.ofM h

/-- **Universal property**: joinLens L M is the least upper bound.
    For any N (combine sym), if both L and M refine N then joinLens
    also refines N. -/
theorem joinLens_is_least {α β γ : Type}
    (L : Lens α) (M : Lens β) (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLN : L.refines N) (hMN : M.refines N) :
    (joinLens L M).refines N := by
  intro r r' h
  have hJE : JoinEquiv L M r r' := (joinLens_kernel L M r r').mp h
  exact JoinEquiv_is_least L M N hNsym hLN hMN r r' hJE

end E213.Hypervisor.Lens.Lattice.Join
