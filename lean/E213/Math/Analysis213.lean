-- E213.Math.Analysis213 — Analysis 213 library entry point.
-- Single-import surface for all 213-native real analysis results.
-- See 213/ANALYSIS213.md (paper) and 213/CATALOG213.md (catalog).
-- Author: Mingu Jeong.  0 sorry, ≤ {propext, Quot.sound}, Mathlib-free.

-- A. Cut Algebra (basic arithmetic)
import E213.Research.Real213CutSum
import E213.Research.Real213CutMul
import E213.Research.Real213CutSumComm
import E213.Research.Real213CutMulComm
import E213.Research.Real213CutSumEq
import E213.Research.Real213CutSumZero
import E213.Research.Real213CutSumOne
import E213.Research.Real213CutMulOne
import E213.Research.Real213CutMidSelf
import E213.Research.Real213CutBisection
import E213.Research.Real213CutDouble
import E213.Research.Real213CutPow
import E213.Research.Real213CutPowConst
import E213.Research.Real213CutPoset

-- B. Dyadic structure
import E213.Research.Real213DyadicBracket
import E213.Research.Real213DyadicTrajectory
import E213.Research.Real213DyadicRiemann

-- C. Differential calculus
import E213.Research.Real213CutFnData
import E213.Research.Real213IsSmooth
import E213.Research.Real213ResolutionDepth
import E213.Research.Real213IsDifferentiable
import E213.Research.Real213DerivativeForms
import E213.Research.Real213DerivativeDepth
import E213.Research.Real213DifferentiableInstances
import E213.Research.Real213DifferentiableHigherPow
import E213.Research.Real213DifferentiableHighOrder
import E213.Research.Real213DifferentiableMid
import E213.Research.Real213DifferentiableAffine
import E213.Research.Real213DifferentiableCompose
import E213.Research.Real213DifferentiableMegaCoverage
import E213.Research.Real213DifferentiationCapstone
import E213.Research.Real213ConcreteDerivativeModulus
import E213.Research.Real213ConcreteDerivativeModulusHigh
import E213.Research.Real213ConcreteDerivativeModulusFinal
import E213.Research.Real213ConcreteDerivativeMega

-- D. Cohomological framework
import E213.Research.Real213FluxCut
import E213.Research.Real213FluxCochain
import E213.Research.Real213FluxDivergence
import E213.Research.Real213FluxMVT
import E213.Research.Real213FluxPolynomial
import E213.Research.Real213FluxCohomologyCapstone
import E213.Research.Real213FluxEquiv
import E213.Research.Real213FluxEquivOps

-- E. MVT witness + Passthrough class
import E213.Research.Real213FluxMVTConcrete
import E213.Research.Real213FluxMVTPolynomial
import E213.Research.Real213FluxMVTHigh
import E213.Research.Real213FluxMVTGeneric
import E213.Research.Real213FluxMVTPassthrough
import E213.Research.Real213FluxMVTApplications
import E213.Research.Real213FluxMVTClosure
import E213.Research.Real213FluxPassthroughClass
import E213.Research.Real213FluxPassthroughCatalog
import E213.Research.Real213FluxMVTWitness
import E213.Research.Real213HasDyadicMVTWitness
import E213.Research.Real213FluxMVTMore
import E213.Research.Real213MVTWitnessCatalog
import E213.Research.Real213MVTWitnessChain
import E213.Research.Real213FluxMVTNested
import E213.Research.Real213FluxMVTNested2
import E213.Research.Real213FluxMVTPattern
import E213.Research.Real213FluxMVTPropagate
import E213.Research.Real213FluxMVTPropagateCompose

-- F. ClassicCalc unified class
import E213.Research.Real213ClassicCalc
import E213.Research.Real213ClassicCalcHigher
import E213.Research.Real213ClassicCalcExtreme
import E213.Research.Real213ClassicCalcGeneric
import E213.Research.Real213ClassicCalcMid
import E213.Research.Real213ClassicCalcCombinators
import E213.Research.Real213ClassicAnti

-- G. Integration / antiderivatives
import E213.Research.Real213Antiderivative
import E213.Research.Real213AntiderivativeCombinators
import E213.Research.Real213AntiderivativeStructural
import E213.Research.Real213IntegralViaAnti
import E213.Research.Real213IntegralProperties
import E213.Research.Real213IndefiniteIntegral
import E213.Research.Real213IntegralIntInterval
import E213.Research.Real213IntegralGeneralInt
import E213.Research.Real213IntegralDyadic

-- H. FTC + Riemann
import E213.Research.Real213FluxFTC
import E213.Research.Real213FluxFTCPolynomial
import E213.Research.Real213FTCRiemann
import E213.Research.Real213FTCRiemannSquare
import E213.Research.Real213FTCRiemannMid
import E213.Research.Real213FTCRiemannGeneric
import E213.Research.Real213FTCRiemannChain

-- I. ODE + physics
import E213.Research.Real213ODELinear
import E213.Research.Real213ODECatalog
import E213.Research.Real213ODESecondOrder
import E213.Research.Real213NewtonFirst
import E213.Research.Real213NewtonSecond
import E213.Research.Real213CubeDerivativeAtZero

-- J. Series + 7 transcendental functions at zero
import E213.Research.Real213CutSequence
import E213.Research.Real213CutSeries
import E213.Research.Real213CutSeriesConst
import E213.Research.Real213CutSeriesZero
import E213.Research.Real213CutGeomSeries
import E213.Research.Real213FluxSeries
import E213.Research.Real213GeomSeriesPartialSum
import E213.Research.Real213ExpAtZero
import E213.Research.Real213SinCosAtZero
import E213.Research.Real213TranscendentalAtZero

-- K. Capstone theorem collection
import E213.Research.Real213PhaseLCapstone
import E213.Research.Real213PhaseACMinimumProposition
import E213.Research.Real213PhaseADCapstone
import E213.Research.Real213PhaseAESuperCapstone
import E213.Research.Real213PhaseAHGrandCapstone
import E213.Research.Real213PhaseANOmegaCapstone
import E213.Research.Real213PhaseBACapstone
import E213.Research.Real213PhaseBHCapstone
import E213.Research.Real213PhaseBQOmegaCapstone
import E213.Research.Real213PhaseBXCapstone
import E213.Research.Real213PhaseCMFinalCapstone
import E213.Research.Real213PhaseCSCapstone
import E213.Research.Real213PhaseDAOmegaOmega
import E213.Research.Real213PhaseDKUltimate

-- L. Bridge to physics track
import E213.Research.Real213PhysicsBridgeNT2

namespace E213.Math.Analysis213

/-!
# Top-level convenience

```lean
import E213.Math.Analysis213
open E213.Research.Real213CutSum

-- 18-fact ULTIMATE capstone covering all 1st-year calculus + ODE + 7 transcendentals
#check @phaseDK_ultimate_capstone
```

Status: 0 sorry, ≤ {propext, Quot.sound}, Mathlib-free.  Lean 4 v4.16.0 core.
-/

end E213.Math.Analysis213

