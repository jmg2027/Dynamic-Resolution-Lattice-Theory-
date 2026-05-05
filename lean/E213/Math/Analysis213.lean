-- E213.Math.Analysis213 — Analysis 213 library entry point.
-- Single-import surface for all 213-native real analysis results.
-- See 213/ANALYSIS213.md (paper) and 213/CATALOG213.md (catalog).
-- Author: Mingu Jeong.  0 sorry, ≤ {propext, Quot.sound}, Mathlib-free.

-- A. Cut Algebra (basic arithmetic)
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutMul
import E213.Math.Real213.CutSumComm
import E213.Math.Real213.CutMulComm
import E213.Math.Real213.CutSumEq
import E213.Math.Real213.CutSumZero
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.CutMulOne
import E213.Math.Real213.CutMidSelf
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutDouble
import E213.Math.Real213.CutPow
import E213.Math.Real213.CutPowConst
import E213.Math.Real213.CutPoset

-- B. Dyadic structure
import E213.Math.Real213.DyadicBracket
import E213.Math.Real213.DyadicTrajectory
import E213.Math.Real213.DyadicRiemann

-- C. Differential calculus
import E213.Math.Real213.CutFnData
import E213.Math.Real213.IsSmooth
import E213.Math.Real213.ResolutionDepth
import E213.Math.Real213.IsDifferentiable
import E213.Math.Real213.DerivativeForms
import E213.Math.Real213.DerivativeDepth
import E213.Math.Real213.DifferentiableInstances
import E213.Math.Real213.DifferentiableMid
import E213.Math.Real213.DifferentiableAffine
import E213.Math.Real213.DifferentiableCompose
import E213.Math.Real213.ConcreteDerivativeModulus

-- D. Cohomological framework
import E213.Math.Real213.FluxCut
import E213.Math.Real213.FluxCochain
import E213.Math.Real213.FluxDivergence
import E213.Math.Real213.FluxMVT
import E213.Math.Real213.FluxPolynomial
import E213.Math.Real213.FluxEquiv
import E213.Math.Real213.FluxEquivOps

-- E. MVT witness + Passthrough class
import E213.Math.Real213.FluxMVTConcrete
import E213.Math.Real213.FluxMVTPolynomial
import E213.Math.Real213.FluxMVTHigh
import E213.Math.Real213.FluxMVTGeneric
import E213.Math.Real213.FluxMVTPassthrough
import E213.Math.Real213.FluxMVTApplications
import E213.Math.Real213.FluxMVTClosure
import E213.Math.Real213.FluxPassthroughClass
import E213.Math.Real213.FluxPassthroughCatalog
import E213.Math.Real213.FluxMVTWitness
import E213.Math.Real213.HasDyadicMVTWitness
import E213.Math.Real213.MVTWitnessCatalog
import E213.Math.Real213.MVTWitnessChain
import E213.Math.Real213.FluxMVTPropagate

-- F. ClassicCalc unified class
import E213.Math.Real213.ClassicCalc
import E213.Math.Real213.ClassicCalcMid
import E213.Math.Real213.ClassicCalcCombinators
import E213.Math.Real213.ClassicAnti

-- G. Integration / antiderivatives
import E213.Math.Real213.Antiderivative
import E213.Math.Real213.AntiderivativeCombinators
import E213.Math.Real213.AntiderivativeStructural
import E213.Math.Real213.IntegralViaAnti
import E213.Math.Real213.IntegralProperties
import E213.Math.Real213.IndefiniteIntegral
import E213.Math.Real213.IntegralIntInterval
import E213.Math.Real213.IntegralGeneralInt
import E213.Math.Real213.IntegralDyadic

-- H. FTC + Riemann
import E213.Math.Real213.FluxFTC
import E213.Math.Real213.FluxFTCPolynomial
import E213.Math.Real213.FTCRiemann
import E213.Math.Real213.FTCRiemannSquare
import E213.Math.Real213.FTCRiemannMid
import E213.Math.Real213.FTCRiemannGeneric
import E213.Math.Real213.FTCRiemannChain

-- I. ODE + physics
import E213.Math.Real213.ODELinear
import E213.Math.Real213.ODECatalog
import E213.Math.Real213.ODESecondOrder
import E213.Math.Real213.NewtonFirst
import E213.Math.Real213.NewtonSecond
import E213.Math.Real213.CubeDerivativeAtZero

-- J. Series + 7 transcendental functions at zero
import E213.Math.Real213.CutSequence
import E213.Math.Real213.CutSeries
import E213.Math.Real213.CutSeriesConst
import E213.Math.Real213.CutSeriesZero
import E213.Math.Real213.CutGeomSeries
import E213.Math.Real213.FluxSeries
import E213.Math.Real213.GeomSeriesPartialSum
import E213.Math.Real213.ExpAtZero
import E213.Math.Real213.SinCosAtZero
import E213.Math.Real213.TranscendentalAtZero

-- K. Capstone theorem collection
import E213.Math.Real213.MinimumProposition

-- L. Bridge to physics track
import E213.Math.Real213.PhysicsBridgeNT2

namespace E213.Math.Analysis213

/-!
# Top-level convenience

```lean
import E213.Math.Analysis213
open E213.Math.Real213.CutSum

-- 18-fact ULTIMATE capstone covering all 1st-year calculus + ODE + 7 transcendentals
#check @phaseDK_ultimate_capstone
```

Status: 0 sorry, ≤ {propext, Quot.sound}, Mathlib-free.  Lean 4 v4.16.0 core.
-/

end E213.Math.Analysis213

