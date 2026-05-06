import E213.Hypervisor.Lens.Kernel.CardinalityLB
import E213.Hypervisor.Lens.Kernel.Congruence
import E213.Hypervisor.Lens.Kernel.Corresp
import E213.Hypervisor.Lens.Kernel.FourDistinct
import E213.Hypervisor.Lens.Kernel.FreeAudit
import E213.Hypervisor.Lens.Kernel.IdLensEq
import E213.Hypervisor.Lens.Kernel.Space
import E213.Hypervisor.Lens.Kernel.SwapInvariant

/-! Spec-as-code entry point for `E213.Hypervisor.Lens.Kernel`.

  Lens algebraic-kernel cluster — the equational layer of the
  Lens theory: equivalences, congruences, cardinality bounds.

  ## Files

    * `Space`         — `KernelSpace` Σ-type over slash-congruences
    * `Corresp`       — Lens kernel ↔ slash-congruence bijection
    * `Congruence`    — slash-congruence definition + closure
    * `IdLensEq`      — id-Lens equivalence class
    * `SwapInvariant` — swap-invariance of the kernel
    * `FourDistinct`  — four-distinct-kernel witness
    * `CardinalityLB` — cardinality lower bound on Lens kernels
    * `FreeAudit`     — free-Lens audit witnesses
-/
