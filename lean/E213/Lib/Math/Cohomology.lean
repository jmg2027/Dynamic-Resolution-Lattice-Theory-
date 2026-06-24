import E213.Lib.Math.Cohomology.Bridge.AlphaEMBridge
import E213.Lib.Math.Cohomology.Examples.BettiKernel
import E213.Lib.Math.Cohomology.Bipartite
import E213.Lib.Math.Cohomology.Capstone
import E213.Lib.Math.Cohomology.ChainComplex
import E213.Lib.Math.Cohomology.DeltaSqZero
import E213.Lib.Math.Cohomology.Bridge.ClosureExtension
import E213.Lib.Math.Cohomology.Cochain
import E213.Lib.Math.Cohomology.Cup
import E213.Lib.Math.Cohomology.CupAW
import E213.Lib.Math.Cohomology.Delta
import E213.Lib.Math.Cohomology.Examples.ColexRoundTrip
import E213.Lib.Math.Cohomology.Examples.XorInvolution
import E213.Lib.Math.Cohomology.Examples.EncodingBijection
import E213.Lib.Math.Cohomology.Examples.EulerClosed
import E213.Lib.Math.Cohomology.Fractal
import E213.Lib.Math.Cohomology.Hodge
import E213.Lib.Math.Cohomology.Examples.K5
import E213.Lib.Math.Cohomology.Examples.NonzeroBetti
import E213.Lib.Math.Cohomology.Bridge.LeibnizFinding
import E213.Lib.Math.Cohomology.Bridge.Paper1Chiral
import E213.Lib.Math.Cohomology.Bridge.Real213Bridge
import E213.Lib.Math.Cohomology.Surfaces
import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Math.Cohomology.Examples.TopologyCompare
import E213.Lib.Math.Cohomology.Bridge.TrivialCases
import E213.Lib.Math.Cohomology.Tripartite
import E213.Lib.Math.Cohomology.Universal
import E213.Lib.Math.Cohomology.Examples.WhyDimFive
import E213.Lib.Math.Cohomology.Bridge.XorPairCombine
import E213.Lib.Math.Cohomology.Bridge.PredicateAsCochain

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology`.

  213-native cohomology: cochains, coboundary δ, cup products,
  Hodge structures, dyadic FSM theory, and the Hodge-conjecture
  bridge stack.  All ∅-axiom on the in-scope files.

  ## Chapters (each = a `<DirName>.lean` umbrella under this dir)

    * `Bipartite/` — K_{NS,NT}^{(c)} bipartite graph cohomology
      (Parametric δ⁰-kernel / Euler-Betti structural family;
      Filled3Cell F₂/Sym(3) H² class; multiplicity-parity orthogonality).
    * `Tripartite/` — K_{NT, det, NS} = K_{2,1,3} tripartite
      cohomology (V213 / V213Betti / shadow projection).
    * `Cochain/`   — Cochain core type + V5 / V5_1 / V5_2
      decomposition lemmas underpinning the cup-AW machinery.
    * `Cup/`       — Strict cup product (Core / Leibniz / Ring).
    * `CupAW/`     — Alexander–Whitney cup-AW: bilinearity,
      Leibniz identities, alg-lift bridges.
    * `Delta/`     — Coboundary δ: Core / Linear / Pointwise /
      SqZero (δ²=0) / V4Capstone.
    * `Fractal/`   — Fractal-level cardinality (AlphaGUT / V25 / Level).
    * `Hodge/`     — Hodge structure: Δ-Laplacian, Star-involution,
      Prop50 / 52 / 53 / 54 capstones.
    * `Universal/` — Prop-level Universal δ²=0 lift (Prop31 …
      Prop53) and Universal.Core / Prop wrappers.

  Note: HodgeConjecture/ was peer-promoted to `Math/HodgeConjecture/`
  in M14 Phase C2 — see that umbrella for the bridge stack.

  All files build clean.  PURE pointwise bilinear formulations
  live at `CupAW/PointwiseBilinear.lean`.
-/
