import E213.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicRiemann
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.DyadicSearch.IVT
import E213.Math.Analysis.DyadicSearch.MinimalRootLens
import E213.Math.Analysis.DyadicSearch.MinimalRootLensMonotone
import E213.Math.Analysis.DyadicSearch.SignedLeftCollapse
import E213.Math.Analysis.DyadicSearch.UnitConsistentOracles

/-! Spec-as-code entry point for `E213.Math.Analysis.DyadicSearch`.

  Dyadic-search Intermediate Value Theorem apparatus.

  ## Foundation

    * `DyadicBracket`     — dyadic bracket-narrowing primitive
    * `DyadicTrajectory`  — sequence of nested dyadic brackets
                            (`alwaysTrue`, `alwaysFalse`, mixed)
    * `DyadicRiemann`     — Riemann-sum interpretation
    * `ConsistentOracle`  — typed protocol: a constructive
                            certificate of the trajectory's
                            finite-resolution commitment
    * `IVT`               — main intermediate-value theorem
                            (constructive bisection IVT for
                            sign-change predicates on cuts)

  ## Trajectory-as-witness IVT (G31 — `research-notes/`)

    * `MinimalRootLens`           — Layer 3a.  213-native form of
                                    the IVT: the bisection trajectory
                                    *is* the root cut.  `signedLeftOracle f`
                                    + `MinimalRootCut` readout +
                                    `IVTRoot` bridge.
    * `MinimalRootLensMonotone`   — Layer 2.  Sign-change invariance
                                    under bisection given
                                    `LocallyDeterminedData f`.
    * `UnitConsistentOracles`     — Layer 3c.  Concrete
                                    `ConsistentOracle` instances on
                                    the unit bracket (alwaysTrue
                                    → leftmost, alwaysFalse →
                                    rightmost).  Demonstrates
                                    non-vacuous inhabitation of
                                    the typed protocol.
    * `SignedLeftCollapse`        — Layer 3c morphism collapse +
                                    §6h composition closure.
                                    `signedLeftOracle f` reduces
                                    structurally to `alwaysTrue`
                                    when f's unit-precision
                                    pattern aligns; the
                                    `CollapseCondition` family is
                                    closed under composition with
                                    `IsResolutionShift`, giving a
                                    `(Nat, +)`-graded module over
                                    resolution shifters.
-/
