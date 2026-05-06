import E213.Math.DyadicFSM.Archive
import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.BitAuto2
import E213.Math.DyadicFSM.BitFSM
import E213.Math.DyadicFSM.Classifier
import E213.Math.DyadicFSM.ConcretePellSig
import E213.Math.DyadicFSM.Conjecture
import E213.Math.DyadicFSM.CrossClassLens
import E213.Math.DyadicFSM.Fib
import E213.Math.DyadicFSM.ForwardClosure
import E213.Math.DyadicFSM.ForwardEventual
import E213.Math.DyadicFSM.ForwardPeriodicity
import E213.Math.DyadicFSM.LCMClosure
import E213.Math.DyadicFSM.Legendre
import E213.Math.DyadicFSM.LucasFSMmod5
import E213.Math.DyadicFSM.Pell
import E213.Math.DyadicFSM.Pisano
import E213.Math.DyadicFSM.ProductFSM
import E213.Math.DyadicFSM.ProductFSMPeriod
import E213.Math.DyadicFSM.ProductFSMPeriodDvd
import E213.Math.DyadicFSM.ProductFSMRun
import E213.Math.DyadicFSM.ProductHelpers
import E213.Math.DyadicFSM.Signature
import E213.Math.DyadicFSM.SignatureBipartite
import E213.Math.DyadicFSM.SignaturePredict
import E213.Math.DyadicFSM.ThueMorse
import E213.Math.DyadicFSM.Tier2Hardness
import E213.Math.DyadicFSM.TierBridge
import E213.Math.DyadicFSM.Trib
import E213.Math.DyadicFSM.TwoLayerPredictor
import E213.Math.DyadicFSM.WalkUniversal

/-! Spec-as-code entry point for `E213.Math.DyadicFSM`.

  Dyadic / FSM theory cluster — the classification engine for
  arithmetic FSM hardness behind the cohomology framework.

  ## Sub-clusters

    * `ArithFSM/`   — arithmetic-FSM family (mod 5..89 + V1/V3/
                      Bound/Equiv/Hardness/Signature/ToBitFSM)
    * `BitFSM/`     — Bool-pred bit-FSM family
    * `Fib/`        — Fibonacci-FSM mod-p variants + Pell relation
                      + Pisano-8 + Pisano capstone
    * `Legendre/`   — Legendre-symbol Pisano variants
    * `Pell/`       — Pell-equation cluster + per-mod variants
    * `Pisano/`     — Pisano-period predictor per base
    * `Trib/`       — Tribonacci variants + CRT4Capstone
    * `Archive/`    — historical / deferred files

  Pre-existing API drift on a small fixed set documented in
  `research-notes/HIERARCHICAL_PLACEMENT.md` §6.3 — see the
  per-sub-cluster umbrella for inline status.
-/
