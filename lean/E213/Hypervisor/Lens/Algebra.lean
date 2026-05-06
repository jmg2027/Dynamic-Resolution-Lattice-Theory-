import E213.Hypervisor.Lens.Algebra.CardinalityLB
import E213.Hypervisor.Lens.Algebra.Congruence
import E213.Hypervisor.Lens.Algebra.Corresp
import E213.Hypervisor.Lens.Algebra.FourDistinct
import E213.Hypervisor.Lens.Algebra.FreeAudit
import E213.Hypervisor.Lens.Algebra.IdLensEq
import E213.Hypervisor.Lens.Algebra.Space
import E213.Hypervisor.Lens.Algebra.SwapInvariant

/-! Spec-as-code entry point for `E213.Hypervisor.Lens.Algebra`.

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
