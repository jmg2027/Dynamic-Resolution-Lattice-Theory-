import E213.Math.Analysis.Integration.Antiderivative
import E213.Math.Analysis.Integration.ClassicAnti
import E213.Math.Analysis.Integration.CutRiemann
import E213.Math.Analysis.Integration.IndefiniteIntegral
import E213.Math.Analysis.Integration.IntegralDyadic
import E213.Math.Analysis.Integration.IntegralGeneralInt
import E213.Math.Analysis.Integration.IntegralIntInterval
import E213.Math.Analysis.Integration.IntegralProperties
import E213.Math.Analysis.Integration.IntegralViaAnti
import E213.Math.Analysis.Integration.Integration

/-! Spec-as-code entry point for `E213.Math.Analysis.Integration`.

  213-native integration theory on cuts.

  ## Riemann + dyadic

    * `CutRiemann`           — Riemann sum on cut intervals
    * `IntegralDyadic`       — dyadic-Riemann integral

  ## Indefinite + interval

    * `IndefiniteIntegral`   — indefinite-integral type
    * `IntegralGeneralInt`   — integration over general intervals
    * `IntegralIntInterval`  — Int-bounded interval variant

  ## Antiderivatives + FTC

    * `Antiderivative`       — antiderivative type
    * `ClassicAnti`          — classical antiderivative rules
    * `IntegralViaAnti`      — integral via antiderivative
                               (fundamental-theorem direction)
    * `IntegralProperties`   — algebraic properties (linearity,
                               additivity over intervals)

  ## Top-level

    * `Integration`          — entry-point catamorphism
-/
