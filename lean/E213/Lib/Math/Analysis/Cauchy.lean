import E213.Lib.Math.Analysis.Cauchy.Wallis
import E213.Lib.Math.Analysis.Cauchy.Euler
import E213.Lib.Math.Analysis.Cauchy.Archimedean
import E213.Lib.Math.Analysis.Cauchy.GenericFamily
import E213.Lib.Math.Analysis.Cauchy.MonotonicBounded
import E213.Lib.Math.Analysis.Cauchy.PellSeq
import E213.Lib.Math.Analysis.Cauchy.ProfiniteSeq
import E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm
import E213.Lib.Math.Analysis.Cauchy.DivergenceLadder
import E213.Lib.Math.Analysis.Cauchy.DivergenceDepth
import E213.Lib.Math.Analysis.Cauchy.DepthPRecursive
import E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances
import E213.Lib.Math.Analysis.Cauchy.DepthPiQuartic
import E213.Lib.Math.Analysis.Cauchy.HurwitzianCF
import E213.Lib.Math.Analysis.Cauchy.PositiveFloorUnbounded
import E213.Lib.Math.Analysis.Cauchy.NonHolonomicWitness
import E213.Lib.Math.Analysis.Cauchy.ZeroRunNonHolonomic
import E213.Lib.Math.Analysis.Cauchy.ZeroRunNonHolonomicWitness
import E213.Lib.Math.Analysis.Cauchy.MorseHedlund
import E213.Lib.Math.Analysis.Cauchy.ThueMorseAperiodic
import E213.Lib.Math.Analysis.Cauchy.HomogRecPeriodic
import E213.Lib.Math.Analysis.Cauchy.NewtonGregory
import E213.Lib.Math.Analysis.Cauchy.PolyDepthMonotone
import E213.Lib.Math.Analysis.Cauchy.ThueMorseRingEscape
import E213.Lib.Math.Analysis.Cauchy.DepthMonotoneSynthesis
import E213.Lib.Math.Analysis.Cauchy.CFiniteHomogRec
import E213.Lib.Math.Analysis.Cauchy.EllipticPeriodicTier
import E213.Lib.Math.Analysis.Cauchy.DetZeroCollapse
import E213.Lib.Math.Analysis.Cauchy.WronskianDepth
import E213.Lib.Math.Analysis.Cauchy.GoldenPiFaces
import E213.Lib.Math.Analysis.Cauchy.ZeroInfinityHole
import E213.Lib.Math.Analysis.Cauchy.QuasiPolyBound
import E213.Lib.Math.Analysis.Cauchy.FiniteDepthAlgebra
import E213.Lib.Math.Analysis.Cauchy.BinomialTransform
import E213.Lib.Math.Analysis.Cauchy.WallisDepthProduct
import E213.Lib.Math.Analysis.Cauchy.DepthTower
import E213.Lib.Math.Analysis.Cauchy.DepthOrdinal
import E213.Lib.Math.Analysis.Cauchy.DepthExponentRecursion
import E213.Lib.Math.Analysis.Cauchy.DepthDoubleExp
import E213.Lib.Math.Analysis.Cauchy.DepthOmegaTower
import E213.Lib.Math.Analysis.Cauchy.DepthLiouvilleCoord
import E213.Lib.Math.Analysis.Cauchy.DepthCeilingResidue
import E213.Lib.Math.Analysis.Cauchy.DepthHeightDiagonal
import E213.Lib.Math.Analysis.Cauchy.DepthFloorDetOne
import E213.Lib.Math.Analysis.Cauchy.DepthOverflowDuality
import E213.Lib.Math.Analysis.Cauchy.ReentryUnit
import E213.Lib.Math.Analysis.Cauchy.DepthClosure
import E213.Lib.Math.Analysis.Cauchy.DepthCoordGenerator
import E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic
import E213.Lib.Math.Analysis.Cauchy.DepthQuadraticGeneric
import E213.Lib.Math.Analysis.Cauchy.DepthCubicGeneric
import E213.Lib.Math.Analysis.Cauchy.CasoratianStep
import E213.Lib.Math.Analysis.Cauchy.CasoratianSigned
import E213.Lib.Math.Analysis.Cauchy.CassiniSigned
import E213.Lib.Math.Analysis.Cauchy.DepthResidueFloor
import E213.Lib.Math.Analysis.Cauchy.DepthSelfReference
import E213.Lib.Math.Analysis.Cauchy.PhiResidueGlue
import E213.Lib.Math.Analysis.Cauchy.PolynomialDepth
import E213.Lib.Math.Analysis.Cauchy.DepthCharacterization
import E213.Lib.Math.Analysis.Cauchy.CassiniDepthFloor
import E213.Lib.Math.Analysis.Cauchy.OrbitDimension
import E213.Lib.Math.Analysis.Cauchy.CFiniteRing
import E213.Lib.Math.Analysis.Cauchy.CFiniteHadamard
import E213.Lib.Math.Analysis.Cauchy.CasoratianRank

/-! Spec-as-code entry point for `E213.Lib.Math.Analysis.Cauchy`.

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

  ## Divergence form, depth, and the resolution-axis tower

  The arc from "a real is a cut" to the foundational residue, each
  link ∅-axiom (narrative: `theory/math/numbersystems/completeness_without_completeness.md`).

    * `EulerDivergenceForm` — cross-determinant `W_n` (discrete
                             Wronskian): φ `±1`, e `−n!`, π Wallis.
    * `DivergenceLadder`,
      `DivergenceDepth`     — finite-difference depth (φ 1, e 3,
                             π 6, Liouville ∞); = P-recursive rank.
    * `DepthPRecursive`     — finite depth ⟺ P-recursive (structural).
    * `DepthPRecursiveInstances`
                            — the witnesses: `newton_polyDepth`
                             (every degree-`d` discrete polynomial has
                             depth `d`, via exact Pascal differences);
                             e's order-1 recurrence + `polyDepth 1`
                             ratio; π's Wallis recurrences + `polyDepth
                             2` step coefficient.
    * `DepthTower`          — the ratio-lift axis (= diff on the
                             exponent); `(h,d)` coordinate.
    * `DepthOrdinal`        — `(h,d)` is an ordinal `< ω²` (`lex_wf`).
    * `DepthExponentRecursion`,
      `DepthDoubleExp`      — third axis = recursion into the
                             exponent; `ratioN` cannot cross one
                             exponential layer (`ε₀` is not the end).
    * `DepthOmegaTower`     — the depth-`r` tower coordinate is an
                             ordinal `< ω^r` (`coord_wf`); the whole
                             `ω^ω` ladder, each layer multiplying the
                             rank by `ω` (`coord_layer_dominates`).
    * `DepthLiouvilleCoord` — `k!` (Liouville exponent, diff-∞)
                             acquires a finite recursion coordinate:
                             `ratioLift fact = n+1`, one diff floors it.
    * `DepthCeilingResidue` — naming the ceiling-raising is a
                             diagonalisation = the residue
                             (`cantor_general`, `self_covering_closure`).
    * `DepthHeightDiagonal` — naming the whole `ω^r` height-tower
                             escapes every finite height
                             (`height_diagonal_escapes`) — the residue at
                             the height scale, the `ε₀`-direction.
    * `DepthOverflowDuality`— the diagonalisation residue and the
                             completeness-break are one operation:
                             a value overflowing the closing bound by
                             the unit `1` either *escapes the family*
                             (`overflow_escapes`, recovers
                             `diag_not_in_seq`) or *breaks domination*
                             (`overflow_breaks` = `overtake_breaks_layer`)
                             — `overflow_dual_reading`.
    * `DepthClosure`        — the finite-coordinate class is closed
                             under `×` and the exponent axis (T3).
    * `DepthCoordGenerator` — the tower is a coordinate system: every
                             coordinate is generated top-down (T4).

  ## Status

  27/27 files included.  All ∅-axiom on the production critical
  path (`tools/scan_axioms.py` — see per-file status notes).
-/
