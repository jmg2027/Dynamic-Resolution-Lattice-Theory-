import E213.Lib.Math.NumberTheory.DyadicFSM.Tier.AlgebraicDegree
import E213.Lib.Math.NumberTheory.DyadicFSM.Archive
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Hierarchy
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModLarge
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1to2
import E213.Lib.Math.NumberTheory.DyadicFSM.BitAuto2
import E213.Lib.Math.NumberTheory.DyadicFSM.BitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Classifier
import E213.Lib.Math.NumberTheory.DyadicFSM.ConcretePellSig
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Conjecture
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.CrossClassLens
import E213.Lib.Math.NumberTheory.DyadicFSM.Fib
import E213.Lib.Math.NumberTheory.DyadicFSM.FibApparitionMod5
import E213.Lib.Math.NumberTheory.DyadicFSM.RankApparition
import E213.Lib.Math.NumberTheory.DyadicFSM.KBonacci
import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardClosure
import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardEventual
import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.LCMClosure
import E213.Lib.Math.NumberTheory.DyadicFSM.Legendre
import E213.Lib.Math.NumberTheory.DyadicFSM.LucasFSMmod5
import E213.Lib.Math.NumberTheory.DyadicFSM.NumberTheory213
import E213.Lib.Math.NumberTheory.DyadicFSM.Pell
import E213.Lib.Math.NumberTheory.DyadicFSM.Pisano
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMPeriod
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMPeriodDvd
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMRun
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductHelpers
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.Signature
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.SignatureBipartite
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.SignaturePredict
import E213.Lib.Math.NumberTheory.DyadicFSM.ThueMorse
import E213.Lib.Math.NumberTheory.DyadicFSM.Tier.Tier2Hardness
import E213.Lib.Math.NumberTheory.DyadicFSM.Tier.TierBridge
import E213.Lib.Math.NumberTheory.DyadicFSM.Trib
import E213.Lib.Math.NumberTheory.DyadicFSM.TwoLayerPredictor
import E213.Lib.Math.NumberTheory.DyadicFSM.Signature.WalkUniversal
import E213.Lib.Math.NumberTheory.DyadicFSM.ContinuedFraction
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Vandermonde
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialSquares
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.PhiFLT
import E213.Lib.Math.NumberTheory.DyadicFSM.KBonacciRecurrence
import E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixCases
import E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixPigeonhole
import E213.Lib.Math.NumberTheory.DyadicFSM.UniversalDispatch

/-! Spec-as-code entry point for `E213.Lib.Math.NumberTheory.DyadicFSM`.

  Dyadic / FSM theory cluster — the classification engine for
  arithmetic FSM hardness behind the cohomology framework.

  ## Sub-clusters

    * `ArithFSM/`   — arithmetic-FSM family (mod 5..89 + V1/V3/
                      Bound/Equiv/Hardness/Signature/ToBitFSM)
    * `BitFSM/`     — Bool-pred bit-FSM family
    * `Fib/`        — Fibonacci-FSM mod-p variants + Pell relation
                      + Pisano-8 + Pisano capstone
    * `KBonacci`    — k-bonacci sequences parametric in `k`
                      (Fibonacci, Tribonacci, Tetranacci, Pentanacci,
                      ...); depth-5 cascade `(d, d-1, NT, 1)`
    * `Legendre`    — Legendre-symbol Pisano variants (single
                      consolidated file)
    * `Pell/`       — Pell-equation cluster + per-mod variants
    * `Pisano/`     — Pisano-period predictor per base
    * `Trib/`       — Tribonacci variants + CRT4Capstone
    * `Archive`     — `EdgeSignature` + `SubwordComplexity`
                      sub-namespaces (single file)

  All files build clean.
-/
