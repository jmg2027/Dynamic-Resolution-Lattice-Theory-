import E213.Hypervisor.Lens.Kernel.Corresp

/-!
# Research.KernelSpace: framework-internal type of slash-congruences

Sigma type over `KernelCorresp.IsSlashCongruence` — the *type-level*
representation of the Lens-kernel space.

## Significance

Type-level foundation of the cardinality question in PAPER1 §5.4.
Determining the cardinality of KernelSpace fixes the position of the
framework.

## Structure

`KernelSpace := Σ (E : Raw → Raw → Prop), IsSlashCongruence E`.
Each element = (slash-congruence + closure proof) pair.

Each Lens L (with commutative combine) embeds into KernelSpace as
(Lens.equiv L, _) (KernelCorresp.lens_kernel_is_slash_cong).

Each KernelSpace element E is realized as the kernel of
`universalLens E` (KernelCorresp.slash_cong_is_lens_kernel).
-/

namespace E213.Hypervisor.Lens.Kernel.Space

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Kernel.Corresp

/-- Type-level representation of the Lens-kernel space. -/
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
  E213.Hypervisor.Lens.Universal.QuotLens.universalLens K.val

end E213.Hypervisor.Lens.Kernel.Space
