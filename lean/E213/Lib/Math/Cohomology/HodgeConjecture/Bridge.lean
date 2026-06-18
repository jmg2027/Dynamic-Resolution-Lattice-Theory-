import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.DiscreteGeometry
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.ClassAExactWitnesses
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.Ising
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.MLDecoder
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.Potts
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.SpinGlass
import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.SpinGlassGroundState

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.HodgeConjecture.Bridge`.

  Bridge layer connecting cup-chain cohomology to statistical-
  mechanics + computer-science models on K_5 / K_{3,2}^{(c=2)}.

  ## Statistical-mechanics models

    * `Ising`              — K_5 Ising-model energy spectrum + routing
    * `Potts`              — q=3 Potts-model variant
    * `SpinGlass`,
      `SpinGlassGroundState` — spin-glass ground-state classification

  ## Discrete geometry

    * `DiscreteGeometry`   — discrete-geometry bridge
    * `ClassAExactWitnesses` — exact-witness vacuity classification

  ## Computer science

    * `MLDecoder`          — ML-decoder bridge (algorithmic
                             interpretation of cup-classes)
-/
