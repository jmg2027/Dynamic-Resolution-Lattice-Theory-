import E213.Math.Analysis.FluxMVT.FTCRiemann
import E213.Math.Analysis.FluxMVT.FluxCochain
import E213.Math.Analysis.FluxMVT.FluxCut
import E213.Math.Analysis.FluxMVT.FluxDivergence
import E213.Math.Analysis.FluxMVT.FluxEquiv
import E213.Math.Analysis.FluxMVT.FluxEquivOps
import E213.Math.Analysis.FluxMVT.FluxFTC
import E213.Math.Analysis.FluxMVT.FluxFTCPolynomial
import E213.Math.Analysis.FluxMVT.FluxMVT
import E213.Math.Analysis.FluxMVT.FluxMVTConcrete
import E213.Math.Analysis.FluxMVT.FluxMVTPassthrough
import E213.Math.Analysis.FluxMVT.FluxMVTPolynomial
import E213.Math.Analysis.FluxMVT.FluxMVTPropagate
import E213.Math.Analysis.FluxMVT.FluxMVTWitness
import E213.Math.Analysis.FluxMVT.FluxMVTWitnessCombinators
import E213.Math.Analysis.FluxMVT.FluxPassthroughCatalog
import E213.Math.Analysis.FluxMVT.FluxPassthroughClass
import E213.Math.Analysis.FluxMVT.FluxPolynomial
import E213.Math.Analysis.FluxMVT.FluxSeries
import E213.Math.Analysis.FluxMVT.HasDyadicMVTWitness
import E213.Math.Analysis.FluxMVT.MVTWitnessCatalog
import E213.Math.Analysis.FluxMVT.MVTWitnessChain

/-! Spec-as-code entry point for `E213.Math.Analysis.FluxMVT` — Flux-form Mean Value Theorem (cohomological).

  Cochains + cuts + divergence + passthrough class + dyadic witnesses + FTC bridge.

  ## Files in this chapter

    * `FTCRiemann`
    * `FluxCochain`
    * `FluxCut`
    * `FluxDivergence`
    * `FluxEquiv`
    * `FluxEquivOps`
    * `FluxFTC`
    * `FluxFTCPolynomial`
    * `FluxMVT`
    * `FluxMVTConcrete`
    * `FluxMVTPassthrough`
    * `FluxMVTPolynomial`
    * `FluxMVTPropagate`
    * `FluxMVTWitness`
    * `FluxMVTWitnessCombinators`
    * `FluxPassthroughCatalog`
    * `FluxPassthroughClass`
    * `FluxPolynomial`
    * `FluxSeries`
    * `HasDyadicMVTWitness`
    * `MVTWitnessCatalog`
    * `MVTWitnessChain`
-/
