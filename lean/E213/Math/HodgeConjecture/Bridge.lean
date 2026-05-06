import E213.Math.HodgeConjecture.Bridge.BeilinsonRegulator
import E213.Math.HodgeConjecture.Bridge.DiscreteGeometry
import E213.Math.HodgeConjecture.Bridge.G6Vacuity
import E213.Math.HodgeConjecture.Bridge.GaloisCounterfactual
import E213.Math.HodgeConjecture.Bridge.Ising
import E213.Math.HodgeConjecture.Bridge.MLDecoder
import E213.Math.HodgeConjecture.Bridge.MotiveEtaleFusion
import E213.Math.HodgeConjecture.Bridge.PhaseRouting
import E213.Math.HodgeConjecture.Bridge.Potts
import E213.Math.HodgeConjecture.Bridge.SpinGlass
import E213.Math.HodgeConjecture.Bridge.SpinGlassGroundState

/-! Spec-as-code entry point for `E213.Math.HodgeConjecture.Bridge`.

  Bridge layer connecting Hodge-conjecture cohomology to physics
  + statistical-mechanics + computer-science models.

  ## Algebraic geometry

    * `BeilinsonRegulator`   — Beilinson regulator construction
    * `MotiveEtaleFusion`    — motive / étale fusion bridge
    * `GaloisCounterfactual` — Galois-action counterfactual

  ## Statistical-mechanics models

    * `Ising`              — Ising-model Hodge-class encoding
    * `Potts`              — Potts-model variant
    * `SpinGlass`,
      `SpinGlassGroundState` — spin-glass ground-state classification

  ## Discrete geometry / phase

    * `DiscreteGeometry`   — discrete-geometry bridge
    * `PhaseRouting`       — phase-routing model
    * `G6Vacuity`          — G6 vacuity claim

  ## Computer science

    * `MLDecoder`          — ML-decoder bridge (algorithmic
                             interpretation of cup-classes)
-/
