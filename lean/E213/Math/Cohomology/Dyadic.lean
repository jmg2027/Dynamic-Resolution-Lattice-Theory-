import E213.Math.Cohomology.Dyadic.Archive
import E213.Math.Cohomology.Dyadic.ArithFSM
import E213.Math.Cohomology.Dyadic.BitAuto2
import E213.Math.Cohomology.Dyadic.BitFSM
import E213.Math.Cohomology.Dyadic.Classifier
import E213.Math.Cohomology.Dyadic.ConcretePellSig
import E213.Math.Cohomology.Dyadic.Conjecture
import E213.Math.Cohomology.Dyadic.CrossClassLens
import E213.Math.Cohomology.Dyadic.Fib
import E213.Math.Cohomology.Dyadic.ForwardClosure
import E213.Math.Cohomology.Dyadic.ForwardEventual
import E213.Math.Cohomology.Dyadic.ForwardPeriodicity
import E213.Math.Cohomology.Dyadic.LCMClosure
import E213.Math.Cohomology.Dyadic.Legendre
import E213.Math.Cohomology.Dyadic.LucasFSMmod5
import E213.Math.Cohomology.Dyadic.Pell
import E213.Math.Cohomology.Dyadic.Pisano
import E213.Math.Cohomology.Dyadic.ProductFSM
import E213.Math.Cohomology.Dyadic.ProductFSMPeriod
import E213.Math.Cohomology.Dyadic.ProductFSMPeriodDvd
import E213.Math.Cohomology.Dyadic.ProductFSMRun
import E213.Math.Cohomology.Dyadic.ProductHelpers
import E213.Math.Cohomology.Dyadic.Signature
import E213.Math.Cohomology.Dyadic.SignatureBipartite
import E213.Math.Cohomology.Dyadic.SignaturePredict
import E213.Math.Cohomology.Dyadic.ThueMorse
import E213.Math.Cohomology.Dyadic.Tier2Hardness
import E213.Math.Cohomology.Dyadic.TierBridge
import E213.Math.Cohomology.Dyadic.Trib
import E213.Math.Cohomology.Dyadic.TwoLayerPredictor
import E213.Math.Cohomology.Dyadic.WalkUniversal

/-! Spec-as-code entry point for `E213.Math.Cohomology.Dyadic`.

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
