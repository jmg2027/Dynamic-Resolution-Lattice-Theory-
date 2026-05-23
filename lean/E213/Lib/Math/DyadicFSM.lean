import E213.Lib.Math.DyadicFSM.Tier.AlgebraicDegree
import E213.Lib.Math.DyadicFSM.Archive
import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.Hierarchy
import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.DyadicFSM.ArithFSM.ModLarge
import E213.Lib.Math.DyadicFSM.ArithFSM.V1to2
import E213.Lib.Math.DyadicFSM.BitAuto2
import E213.Lib.Math.DyadicFSM.BitFSM
import E213.Lib.Math.DyadicFSM.Signature.Classifier
import E213.Lib.Math.DyadicFSM.ConcretePellSig
import E213.Lib.Math.DyadicFSM.Signature.Conjecture
import E213.Lib.Math.DyadicFSM.Product.CrossClassLens
import E213.Lib.Math.DyadicFSM.Fib
import E213.Lib.Math.DyadicFSM.Forward.ForwardClosure
import E213.Lib.Math.DyadicFSM.Forward.ForwardEventual
import E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
import E213.Lib.Math.DyadicFSM.Product.LCMClosure
import E213.Lib.Math.DyadicFSM.Legendre
import E213.Lib.Math.DyadicFSM.LucasFSMmod5
import E213.Lib.Math.DyadicFSM.NumberTheory213
import E213.Lib.Math.DyadicFSM.Pell
import E213.Lib.Math.DyadicFSM.Pisano
import E213.Lib.Math.DyadicFSM.Product.ProductFSM
import E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriod
import E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriodDvd
import E213.Lib.Math.DyadicFSM.Product.ProductFSMRun
import E213.Lib.Math.DyadicFSM.Product.ProductHelpers
import E213.Lib.Math.DyadicFSM.Signature.Signature
import E213.Lib.Math.DyadicFSM.Signature.SignatureBipartite
import E213.Lib.Math.DyadicFSM.Signature.SignaturePredict
import E213.Lib.Math.DyadicFSM.ThueMorse
import E213.Lib.Math.DyadicFSM.Tier.Tier2Hardness
import E213.Lib.Math.DyadicFSM.Tier.TierBridge
import E213.Lib.Math.DyadicFSM.Trib
import E213.Lib.Math.DyadicFSM.TwoLayerPredictor
import E213.Lib.Math.DyadicFSM.Signature.WalkUniversal

/-! Spec-as-code entry point for `E213.Lib.Math.DyadicFSM`.

  Dyadic / FSM theory cluster — the classification engine for
  arithmetic FSM hardness behind the cohomology framework.

  ## Sub-clusters

    * `ArithFSM/`   — arithmetic-FSM family (mod 5..89 + V1/V3/
                      Bound/Equiv/Hardness/Signature/ToBitFSM)
    * `BitFSM/`     — Bool-pred bit-FSM family
    * `Fib/`        — Fibonacci-FSM mod-p variants + Pell relation
                      + Pisano-8 + Pisano capstone
    * `Legendre`    — Legendre-symbol Pisano variants (single
                      consolidated file)
    * `Pell/`       — Pell-equation cluster + per-mod variants
    * `Pisano/`     — Pisano-period predictor per base
    * `Trib/`       — Tribonacci variants + CRT4Capstone
    * `Archive`     — historical sub-cluster (single file post
                      consolidation): `EdgeSignature`
                      + `SubwordComplexity` sub-namespaces

  All files build clean.  The deferred-cluster repair (`lean/E213/docs/HIERARCHICAL_PLACEMENT.md` §6.3) is
  closed.
-/
