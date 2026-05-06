import E213.Lib.Math.HodgeConjecture.API
import E213.Lib.Math.HodgeConjecture.Bridge
import E213.Lib.Math.HodgeConjecture.Foundation
import E213.Lib.Math.HodgeConjecture.MotivicBridge
import E213.Lib.Math.HodgeConjecture.Pairing
import E213.Lib.Math.HodgeConjecture.Refinement
import E213.Lib.Math.HodgeConjecture.Structure
import E213.Lib.Math.HodgeConjecture.Toolkit

/-! Spec-as-code entry point for `E213.Lib.Math.HodgeConjecture`.

  213-native Hodge-conjecture bridge stack.

  ## Top-level

    * `API.lean` — public surface

  ## Sub-cluster umbrellas

    * `Foundation/`  — Canonical / Complete / Conjecture /
                       ConjectureLens / Filled / LensCata
    * `Structure/`   — algebraic structure (HardLefschetz, Map,
                       PoincareDuality, Ring)
    * `Pairing/`     — Hodge index / Hodge–Riemann pairings
    * `Refinement/`  — cup-atomic, generalized Hodge,
                       Lefschetz hyperplane / (1,1), standard
                       conjectures, Voisin
    * `Toolkit/`     — LensClassifier, Primitives, RoundTrip*
    * `Bridge/`      — physics / CS bridges: Beilinson regulator,
                       discrete geometry, G6 vacuity, Galois
                       counterfactual, Ising, ML decoder, motive
                       etale fusion, phase routing, Potts, spin
                       glass (+ ground state)
    * `MotivicBridge/` — motivic-cohomology bridges (classical-side
                         counterparts): Beilinson-Lichtenbaum,
                         Bloch-Beilinson, ChernCharacter, HodgeTate,
                         MumfordTate, Tate.  Hosted under OS/ before
                         Phase A3.
-/
