import E213.Lib.Math.HodgeConjecture.Structure.HardLefschetz
import E213.Lib.Math.HodgeConjecture.Structure.HardLefschetzT2Squared
import E213.Lib.Math.HodgeConjecture.Structure.Map
import E213.Lib.Math.HodgeConjecture.Structure.PoincareDuality
import E213.Lib.Math.HodgeConjecture.Structure.Ring

/-! Spec-as-code entry point for `E213.Lib.Math.HodgeConjecture.Structure`.

  Algebraic structure of H*: cohomology ring, Poincaré duality,
  hard Lefschetz, and the structural map ϕ.

  ## Files

    * `Ring`                     — H* ring structure
    * `Map`                      — structural map ϕ : H* → image
    * `PoincareDuality`          — Poincaré-duality pairing
    * `HardLefschetz`            — base capstone on Δ⁴
                                   (`⋆⋆ = id` ⟺ HL in ℤ/2)
    * `HardLefschetzT2Squared`   — ★ Non-vacuous lift to T²×T²
                                   (real dim 4 = complex dim 2):
                                   `L²` mult-by-2 on H⁰→H⁴,
                                   `L` 4×4 permutation det=+1
                                   on H¹→H³.  G10 Phase 2
                                   follow-up closed.
-/
