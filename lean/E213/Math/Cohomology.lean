import E213.Math.Cohomology.AlphaEMBridge
import E213.Math.Cohomology.BettiKernel
import E213.Math.Cohomology.Bipartite
import E213.Math.Cohomology.Capstone
import E213.Math.Cohomology.ClosureExtension
import E213.Math.Cohomology.Cochain
import E213.Math.Cohomology.Cup
import E213.Math.Cohomology.CupAW
import E213.Math.Cohomology.Delta
import E213.Math.Cohomology.DiamondAudit
import E213.Math.Cohomology.DiamondShape
import E213.Math.Cohomology.Dyadic
import E213.Math.Cohomology.EncodingBijection
import E213.Math.Cohomology.EncodingBijection52
import E213.Math.Cohomology.EulerClosed
import E213.Math.Cohomology.Fractal
import E213.Math.Cohomology.Hodge
import E213.Math.Cohomology.HodgeConjecture
import E213.Math.Cohomology.K5
import E213.Math.Cohomology.LeibnizFinding
import E213.Math.Cohomology.Paper1Chiral
import E213.Math.Cohomology.Real213Bridge
import E213.Math.Cohomology.SimplexBasis
import E213.Math.Cohomology.TopologyCompare
import E213.Math.Cohomology.TrivialCases
import E213.Math.Cohomology.Universal
import E213.Math.Cohomology.WhyDimFive
import E213.Math.Cohomology.XorPairCombine

/-! Spec-as-code entry point for `E213.Math.Cohomology`.

  213-native cohomology: cochains, coboundary δ, cup products,
  Hodge structures, dyadic FSM theory, and the Hodge-conjecture
  bridge stack.  All ∅-axiom on the in-scope files.

  ## Chapters (each = a `<DirName>.lean` umbrella under this dir)

    * `Bipartite/` — K_{NS,NT}^{(c)} bipartite graph cohomology
      (V32 / V32Betti / Filled — 2-cell-filling of 4-cycles).
    * `Cochain/`   — Cochain core type + V5 / V5_1 / V5_2
      decomposition lemmas underpinning the cup-AW machinery.
    * `Cup/`       — Strict cup product (Core / Leibniz / Ring).
    * `CupAW/`     — Alexander–Whitney cup-AW: bilinearity,
      Leibniz identities, alg-lift bridges.
    * `Delta/`     — Coboundary δ: Core / Linear / Pointwise /
      SqZero (δ²=0) / V4Capstone.
    * `Dyadic/`    — Dyadic / FSM / Pell / Pisano / Trib /
      Legendre / WalkUniversal sub-cluster.  The classification
      engine for arithmetic FSM hardness.
    * `Fractal/`   — Fractal-level cardinality (AlphaGUT / V25 / Level).
    * `Hodge/`     — Hodge structure: Δ-Laplacian, Star-involution,
      Prop50 / 52 / 53 / 54 capstones.
    * `HodgeConjecture/` — Hodge-conjecture bridge stack.
    * `Universal/` — Prop-level Universal δ²=0 lift (Prop31 …
      Prop53) and Universal.Core / Prop wrappers.

  Pre-existing API drift on a small fixed set of files documented
  in `research-notes/HIERARCHICAL_PLACEMENT.md` §6.3.  Each
  sub-cluster umbrella records its own deferred list inline.
-/
