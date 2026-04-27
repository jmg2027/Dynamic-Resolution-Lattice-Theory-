import E213.Hypervisor.Lens
import E213.Research.KernelCongruence

/-!
# Research.JoinEquiv: smallest slash-congruence as the join of two Lens kernels

**Claim**: for two Lenses L and M, JoinEquiv L M is the smallest
**slash-congruence equivalence relation** containing L.equiv ∪ M.equiv.

## Inductive definition

Equivalence structure + slash-congruence are built in as constructors.

This corresponds to the **Join (least upper bound)** of the refines
preorder — the smallest congruence that refines both kernels.
-/

namespace E213.Research.JoinEquiv

open E213.Firmware E213.Hypervisor

/-- Smallest slash-congruence containing the kernels of two Lenses. -/
inductive JoinEquiv {α β : Type} (L : Lens α) (M : Lens β) : Raw → Raw → Prop where
  | ofL : L.equiv x y → JoinEquiv L M x y
  | ofM : M.equiv x y → JoinEquiv L M x y
  | refl (x : Raw) : JoinEquiv L M x x
  | symm : JoinEquiv L M x y → JoinEquiv L M y x
  | trans :
      JoinEquiv L M x y → JoinEquiv L M y z → JoinEquiv L M x z
  | slash_cong
      (hxy : x ≠ y) (hx'y' : x' ≠ y') :
      JoinEquiv L M x x' → JoinEquiv L M y y' →
      JoinEquiv L M (Raw.slash x y hxy) (Raw.slash x' y' hx'y')

/-- JoinEquiv contains L.equiv. -/
theorem L_refines_JoinEquiv {α β : Type} (L : Lens α) (M : Lens β)
    (x y : Raw) (h : L.equiv x y) : JoinEquiv L M x y :=
  JoinEquiv.ofL h

/-- JoinEquiv contains M.equiv. -/
theorem M_refines_JoinEquiv {α β : Type} (L : Lens α) (M : Lens β)
    (x y : Raw) (h : M.equiv x y) : JoinEquiv L M x y :=
  JoinEquiv.ofM h

/-- JoinEquiv is a slash-congruence (directly from the constructor). -/
theorem JoinEquiv_slash_cong {α β : Type} (L : Lens α) (M : Lens β)
    (x x' y y' : Raw) (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hxx' : JoinEquiv L M x x') (hyy' : JoinEquiv L M y y') :
    JoinEquiv L M (Raw.slash x y hxy) (Raw.slash x' y' hx'y') :=
  JoinEquiv.slash_cong hxy hx'y' hxx' hyy'

end E213.Research.JoinEquiv

namespace E213.Research.JoinEquiv

open E213.Firmware E213.Hypervisor
open E213.Research.KernelCongruence

/-- **Join universal property**: if both L and M refine N (i.e.,
    N.equiv contains both L.equiv and M.equiv) and N's combine is
    symmetric, then N.equiv also contains JoinEquiv L M.

    That is, JoinEquiv L M is the **minimum** relation among those
    satisfying "L.refines N ∧ M.refines N" (least upper bound in
    the refines preorder). -/
theorem JoinEquiv_is_least {α β γ : Type} (L : Lens α) (M : Lens β) (N : Lens γ)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (hLN : L.refines N) (hMN : M.refines N) :
    ∀ x y : Raw, JoinEquiv L M x y → N.equiv x y := by
  intro x y h
  induction h with
  | ofL h => exact hLN _ _ h
  | ofM h => exact hMN _ _ h
  | refl x => exact Lens.equiv_refl N x
  | symm _ ih => exact Lens.equiv_symm N ih
  | trans _ _ ih1 ih2 => exact Lens.equiv_trans N ih1 ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact Lens.equiv_slash_congruence N hNsym _ _ _ _ hxy hx'y' ih1 ih2

end E213.Research.JoinEquiv
