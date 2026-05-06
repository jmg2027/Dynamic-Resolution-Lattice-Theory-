import E213.Lib.Math.Tactic.HurwitzRing
import E213.Lib.Math.Tactic.IntSquare
import E213.Lib.Math.Tactic.QuadExtension
import E213.Lib.Math.Tactic.Test.IntSquareTest
import E213.Lib.Math.Tactic.Test.QuadExtensionTest

/-! Spec-as-code entry point for `E213.Lib.Math.Tactic`.

  213-native math tactics — one notch above `Kernel/Tactic/`
  (Omega213, QuadNorm, Pow213, …) since these tactics target
  the CayleyDickson / ZSqrt typeclass ecosystem.

  ## Tactics

    * `IntSquare`     — Diophantine integer-square identities.
    * `QuadExtension` — `quad_extension D` macro that emits
                        a one-line `ConjugationCodomain (ZSqrt D)`
                        instance for any positive D.  Replaces
                        the per-D structure boilerplate.
    * `HurwitzRing`   — `hurwitz_ring` tactic for Hurwitz norm-
                        multiplicativity identities at arbitrary
                        Cayley-Dickson layers (still extending
                        coverage; some Heavy-variant goals deferred).

  ## Tests

    * `Test/IntSquareTest`     — `quad_norm`-shape sanity check.
    * `Test/QuadExtensionTest` — full register + verify pipeline
                                 for D = 11, 13, 17.
-/
