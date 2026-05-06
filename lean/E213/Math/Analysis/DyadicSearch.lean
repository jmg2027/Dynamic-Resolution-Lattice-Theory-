import E213.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicRiemann
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.DyadicSearch.IVT

/-! Spec-as-code entry point for `E213.Math.Analysis.DyadicSearch`.

  Dyadic-search Intermediate Value Theorem apparatus.

  ## Files

    * `DyadicBracket`     — dyadic bracket-narrowing primitive
    * `DyadicTrajectory`  — sequence of nested dyadic brackets
    * `DyadicRiemann`     — Riemann-sum interpretation
    * `ConsistentOracle`  — consistency oracle on Bool-valued
                            decision sequences
    * `IVT`               — main intermediate-value theorem
                            (constructive bisection IVT for
                            sign-change predicates on cuts)
-/
