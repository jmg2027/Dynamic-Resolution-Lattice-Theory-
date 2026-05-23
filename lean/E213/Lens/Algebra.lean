import E213.Lens.Algebra.Congruence
import E213.Lens.Algebra.Corresp
import E213.Lens.Internal.Algebra.FourDistinct
import E213.Lens.Internal.Algebra.FreeAudit
import E213.Lens.Algebra.IdLensEq
import E213.Lens.Internal.Algebra.Space
import E213.Lens.Internal.Algebra.SwapInvariant

/-! Spec-as-code entry point for `E213.Lens.Algebra`.

  Lens algebraic-kernel cluster — the equational layer of the
  Lens theory: equivalences, congruences.

  Cardinality results (`LensCardinality`, `CardinalityLB`) live
  in `Lens/Cardinality/`.
## Files

    * `Space`         — `KernelSpace` Σ-type over slash-congruences
    * `Corresp`       — Lens kernel ↔ slash-congruence bijection
    * `Congruence`    — slash-congruence definition + closure
    * `IdLensEq`      — id-Lens equivalence class
    * `SwapInvariant` — swap-invariance of the kernel
    * `FourDistinct`  — four-distinct-kernel witness
    * `FreeAudit`     — free-Lens audit witnesses

  ## INDEX.md

  See `Algebra/INDEX.md` for cluster details.
-/
