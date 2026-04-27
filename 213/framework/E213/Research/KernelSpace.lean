import E213.Research.KernelCorresp

/-!
# Research.KernelSpace: framework-internal type of slash-congruences

`KernelCorresp.IsSlashCongruence` 위 의 sigma type — Lens-kernel
space 의 *type-level* representation.

## 의의

PAPER1 §5.4 의 cardinality question 의 *type-level* foundation.
KernelSpace 의 cardinality 결정 = framework 의 위치 fix.

## 구조

`KernelSpace := Σ (E : Raw → Raw → Prop), IsSlashCongruence E`.
각 element = (slash-congruence + closure proof) pair.

각 Lens L (commutative combine) 가 (Lens.equiv L, _) 로 KernelSpace 에
embed (KernelCorresp.lens_kernel_is_slash_cong).

각 KernelSpace element E 가 `universalLens E` 의 kernel 로 realize
(KernelCorresp.slash_cong_is_lens_kernel).
-/

namespace E213.Research.KernelSpace

open E213.Firmware E213.Hypervisor
open E213.Research.KernelCorresp

/-- Lens-kernel space 의 type-level representation. -/
def KernelSpace : Type := { E : Raw → Raw → Prop // IsSlashCongruence E }

/-- Two KernelSpace elements are equal iff their relations are equal. -/
theorem KernelSpace.ext {K1 K2 : KernelSpace} (h : K1.val = K2.val) : K1 = K2 :=
  Subtype.ext h

/-- Lens (with commutative combine) → KernelSpace embedding. -/
def fromLens {α : Type} (L : Lens α)
    (hsym : ∀ u v, L.combine u v = L.combine v u) : KernelSpace :=
  ⟨L.equiv, lens_kernel_is_slash_cong L hsym⟩

/-- KernelSpace → Lens (Raw → Prop) realisation via universalLens. -/
def toLens (K : KernelSpace) : Lens (Raw → Prop) :=
  E213.Research.UniversalQuotLens.universalLens K.val

end E213.Research.KernelSpace
