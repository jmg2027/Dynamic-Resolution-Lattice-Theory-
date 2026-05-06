import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndex
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeIndexT2
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeRiemann
import E213.Lib.Math.HodgeConjecture.Pairing.HodgeRiemannT2

/-! Spec-as-code entry point for `E213.Lib.Math.HodgeConjecture.Pairing`.

  Pairings on H* — Hodge index + Hodge–Riemann.

  ## Files

    * `HodgeIndex`     — base capstone on K_{3,2}^{(c=2)}
                         (graph; cup-pairing vacuously zero)
    * `HodgeIndexT2`   — non-vacuous lift to T² minimal CW
                         (signature (1, 1) by direct ℤ-decide)
    * `HodgeRiemann`   — base capstone on K_{3,2}^{(c=2)}
                         (positivity vacuous in ℤ/2)
    * `HodgeRiemannT2` — non-vacuous lift: Kähler class with
                         `cup(ω, ω) > 0` on T² + signature
                         decomposition

  ## Status

  Both the base ℤ/2-vacuous form and the T² ℚ²¹³-refined non-vacuous
  form are now strict ∅-axiom (G10 Phase 2 follow-up closed).
-/
