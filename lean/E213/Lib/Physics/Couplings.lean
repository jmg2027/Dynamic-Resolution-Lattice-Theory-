import E213.Lib.Physics.Couplings.AlphaGUT
import E213.Lib.Physics.Couplings.AsymptoticFreedom
import E213.Lib.Physics.Couplings.ClosedPropagator
import E213.Lib.Physics.Couplings.ColorConfinement
import E213.Lib.Physics.Couplings.DysonStructure
import E213.Lib.Physics.Couplings.GUTUnification
import E213.Lib.Physics.Couplings.PhotonKernel
import E213.Lib.Physics.Couplings.RunningGap
import E213.Lib.Physics.Couplings.SpectrumComplete
import E213.Lib.Physics.Couplings.ThetaQCD
import E213.Lib.Physics.Couplings.TripleCoupling

/-! Spec-as-code entry point for `E213.Lib.Physics.Couplings`.

  Gauge-coupling cluster — α_GUT, α_3 (strong), α_2 (weak),
  unification, propagator structure.

  ## Couplings + unification

    * `AlphaGUT`            — α_GUT = 6/(25π²) ≈ 0.02433
    * `GUTUnification`      — running-coupling unification scale
    * `TripleCoupling`      — α_1 / α_2 / α_3 triple structure

  ## Strong / colour

    * `ColorConfinement`    — colour-confinement structural witness
    * `AsymptoticFreedom`   — β-function negative leading term
    * `SpectrumComplete`    — full coupling-spectrum closure

  ## Propagator + Dyson

    * `PhotonKernel`        — photon two-point kernel
    * `ClosedPropagator`    — closed-form propagator factor
    * `DysonStructure`      — Dyson-tail summation
    * `RunningGap`          — running gap profile

  ## CP-violation

    * `ThetaQCD`            — θ_QCD < J·α⁴ falsifier target
-/
