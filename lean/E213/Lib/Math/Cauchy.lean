import E213.Lib.Math.Cauchy.Wallis
import E213.Lib.Math.Cauchy.Euler
import E213.Lib.Math.Cauchy.Archimedean
import E213.Lib.Math.Cauchy.GenericFamily
import E213.Lib.Math.Cauchy.MonotonicBounded
import E213.Lib.Math.Cauchy.PellSeq
import E213.Lib.Math.Cauchy.ProfiniteSeq

/-! Spec-as-code entry point for `E213.Lib.Math.Cauchy`.

  213-native Cauchy / Euler / Wallis / Pell sequences and their
  convergence proofs.  Companion to `Math.Real213` (the type) +
  `Math.Analysis.CauchyComplete` (the completeness theorem).

  ## Foundations

    * `Archimedean`        — Archimedean Cauchy completion via
                             Dedekind cut on abLens projections.
                             `OrderCauchyData`, `RealCut`.
    * `MonotonicBounded`   — generalisation: ab-monotonic sequence
                             ⇒ `isOrderCauchy` for every (m, k).
    * `GenericFamily`      — unified Lens + post-processing.
    * `ProfiniteSeq`       — Cauchy on the `leavesModNat` family
                             (used by `Math.Hyper.Padic`).

  ## Concrete transcendentals

    * `EulerSeq`           — e via Σ 1/k!.  e ∈ (2, 3) cuts.
    * `EulerCombinatorialPure`,
      `EulerGenericPure`,
      `EulerSharper`,
      `EulerSharperKernelFree`,
      `EulerSharperPure`   — successively sharper bounds for e.
    * `WallisSeq`          — π/2 via Wallis product.  π/2 ∈ (1, 2).
    * `WallisSharper`,
      `WallisSharperKernelFree` — sharper Wallis bounds.

  ## Algebraic / number-theoretic

    * `PellSeq`            — Pell sequence Raw construction.

  ## Status

  14/14 files included.  All ∅-axiom on the production critical
  path (`tools/scan_axioms.py` — see per-file status notes).
-/
