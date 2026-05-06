import E213.Math.Analysis.FluxMVT.DyadicMVTWitness
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
import E213.Math.Analysis.FluxMVT.MVTWitnessCatalog
import E213.Math.Analysis.FluxMVT.MVTWitnessChain

/-! Spec-as-code entry point for `E213.Math.Analysis.FluxMVT`.

  Flux-form Mean Value Theorem — a 213-native, cohomological
  reformulation of MVT that tracks "flux through endpoints"
  rather than tangent slopes.

  ## Flux core

    * `FluxCut`           — flux as a cut-level value
    * `FluxCochain`       — flux as a Cochain (cohomological)
    * `FluxDivergence`    — divergence theorem at cut level
    * `FluxEquiv`,
      `FluxEquivOps`      — flux-equivalence relation + ops

  ## MVT witnesses

    * `FluxMVT`                       — generic flux-MVT
    * `FluxMVTConcrete`               — concrete witness
    * `FluxMVTWitness`,
      `FluxMVTWitnessCombinators`     — witness builders
    * `MVTWitnessCatalog`,
      `MVTWitnessChain`               — catalogue + chain
    * `DyadicMVTWitness`              — dyadic-bracket variant

  ## Polynomial / passthrough

    * `FluxPolynomial`,
      `FluxMVTPolynomial`,
      `FluxFTCPolynomial`             — polynomial-input variants
    * `FluxMVTPassthrough`,
      `FluxPassthroughCatalog`,
      `FluxPassthroughClass`          — passthrough machinery
    * `FluxMVTPropagate`              — propagation lemmas

  ## FTC + series

    * `FluxFTC`           — fundamental-theorem-of-calculus
                            in flux form
    * `FTCRiemann`        — Riemann-form FTC
    * `FluxSeries`        — flux applied to series
-/
