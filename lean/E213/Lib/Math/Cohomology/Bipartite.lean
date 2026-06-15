import E213.Lib.Math.Cohomology.Bipartite.Filled
import E213.Lib.Math.Cohomology.Bipartite.V32
import E213.Lib.Math.Cohomology.Bipartite.V32Betti
import E213.Lib.Math.Cohomology.Bipartite.V32LocalSignature
import E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.BettiOneUniversal
import E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.PathCoboundary
import E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.KEdgeCochain
import E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.KerSizeUniversal
import E213.Lib.Math.Cohomology.Bipartite.AdemUniversal
import E213.Lib.Math.Cohomology.Bipartite.Filled5CellExtension
import E213.Lib.Math.Cohomology.Bipartite.MasseyAlternatingUniversal
import E213.Lib.Math.Cohomology.Bipartite.MasseyTripleOmega
import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcMaster
import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcUniversal
import E213.Lib.Math.Cohomology.Bipartite.Parametric.PellOrbitInstances
import E213.Lib.Math.Cohomology.Bipartite.V22
import E213.Lib.Math.Cohomology.Bipartite.V31c2
import E213.Lib.Math.Cohomology.Bipartite.V33EnrichedParametricDualSpanHardLift
import E213.Lib.Math.Cohomology.Bipartite.V33Mult1Trivial
import E213.Lib.Math.Cohomology.Bipartite.V33c3Enriched
import E213.Lib.Math.Cohomology.Bipartite.V33c3Indeterminacy
import E213.Lib.Math.Cohomology.Bipartite.OctetCokernel

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Bipartite`.

  K_{NS,NT}^{(c)} bipartite-graph cohomology.

  ## Files

    * `V32`               — K_{3,2}^{(2)} concrete instance: vertex set,
                            edges, simplicial structure
    * `V32Betti`          — Betti numbers b_0 / b_1 of K_{3,2}^{(2)}
                            (the 1-skeleton case: b_1 = 8, b_k = 0 for k ≥ 2)
    * `V32LocalSignature` — (2, 1, 3) atomic multiset reproduced at
                            every vertex / edge / face of K_{3,2}^{(c=2)};
                            master `local_213_at_every_point`.
    * `Filled`            — 2-cell-filled extension: filling 4-cycles
                            reduces b_1 by 1 per cell.  Capstone:
                            b_1 ∈ {8, 7, 6, 5} as 0–3 simple 4-cycles
                            are filled.
-/
