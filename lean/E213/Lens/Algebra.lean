import E213.Lens.Algebra.CardinalityLB
import E213.Lens.Algebra.Congruence
import E213.Lens.Internal.Algebra.FourDistinct
import E213.Lens.Internal.Algebra.FreeAudit
import E213.Lens.Algebra.IdLensEq
import E213.Lens.Internal.Algebra.SwapInvariant

/-! Spec-as-code entry point for `E213.Lens.Algebra`.

  Lens algebraic-kernel cluster — the equational layer of the
  Lens theory: equivalences, congruences, cardinality bounds.

  Removed (design-by-funext/propext 금지):
    * `Algebra.Corresp` — Lens kernel ↔ slash-congruence bijection
                          (used `universalLens (Raw → Prop)`)
    * `Internal.Algebra.Space` — KernelSpace Σ-type via `universalLens`

  ## Remaining Files

    * `Congruence`    — slash-congruence definition + closure (relation)
    * `IdLensEq`      — id-Lens equivalence class
    * `SwapInvariant` — swap-invariance of the kernel
    * `FourDistinct`  — four-distinct-kernel witness
    * `CardinalityLB` — cardinality lower bound on Lens kernels
    * `FreeAudit`     — free-Lens audit witnesses
-/
