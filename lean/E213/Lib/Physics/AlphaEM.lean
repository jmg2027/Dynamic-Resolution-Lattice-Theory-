import E213.Lib.Physics.AlphaEM.Augmented
import E213.Lib.Physics.AlphaEM.Bare
import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.AlphaEM.Capstone
import E213.Lib.Physics.AlphaEM.ChannelCohomologyLoss
import E213.Lib.Physics.AlphaEM.CupChannelInventory
import E213.Lib.Physics.AlphaEM.CupRingTrace
import E213.Lib.Physics.AlphaEM.GradedDecomposition
import E213.Lib.Physics.AlphaEM.FractalLevelLift
import E213.Lib.Physics.AlphaEM.FractalLevelZetaSpectrum
import E213.Lib.Physics.AlphaEM.FractalLevelZetaConvergence
import E213.Lib.Physics.AlphaEM.FractalLevelZetaBracket
import E213.Lib.Physics.AlphaEM.GradedFormula
import E213.Lib.Physics.AlphaEM.GradedFormulaPrecision
import E213.Lib.Physics.AlphaEM.GramSelfConsistency
import E213.Lib.Physics.AlphaEM.GramHigherOrder
import E213.Lib.Physics.AlphaEM.GramStructuralCapstone
import E213.Lib.Physics.AlphaEM.FractalLevelZetaCoeffSeq
import E213.Lib.Physics.AlphaEM.FractalLevelZetaModulus
import E213.Lib.Physics.AlphaEM.LaplacianSpectrum
import E213.Lib.Physics.AlphaEM.PiFiveGap
import E213.Lib.Physics.AlphaEM.ProjectionRatios
import E213.Lib.Physics.AlphaEM.StructuralGap

/-! Spec-as-code entry point for E213.Lib.Physics.AlphaEM.

  1/α_em derivation cluster — topical files:

  * `Augmented.lean`            — Dyson tail + SO(10) + Gram self-energy bracket
  * `Bare.lean`                 — atomic integers + lattice prefactors + 5-term
  * `Brackets.lean`             — bare/tight/V137 rational brackets
  * `Capstone.lean`             — unified-sum + simplicial decomp + master
  * `ChannelCohomologyLoss.lean`— K↪Δ⁴ topological loss: H¹(K)=8,
                                  χ(Δ⁴,K)=8, six-fold equivalence
                                  1/α_3 = NS²-1 = 8 = dim H¹(K)
                                  = χ_rel = ζ_K(0) = E−V+1.  Plus
                                  atomic constants consistency
                                  c·NS·NT = NS²+NS+NT−2 (213=min
                                  non-trivial solution at NT=2).
  * `CupChannelInventory.lean`  — Δ⁴ cup-channel finite enumeration
                                  (Step A): 10 / 80 / 785 channels
  * `CupRingTrace.lean`         — bottom-up cup-ring functional tests
                                  (Test 1): F₁..F₅ — none give 137,
                                  pointing to the Laplacian channel
  * `GradedDecomposition.lean`  — 5-fold output-grade decomposition
                                  of the 785 cross-terms
                                  (25/100/200/250/210), with three
                                  structural properties: topological
                                  grade isolation, chirality
                                  (cup non-commutativity), and top
                                  hard wall (binom 5 k = 0 for k≥6).
                                  STRICT ∅-AXIOM.
  * `LaplacianSpectrum.lean`    — finite ζ-analog via cochain Laplacian
                                  (Test 2): Δ⁴ rank=30 uniform ev=5,
                                  ζ_Δ(2)=6/5; K_{3,2}^{(c=2)} spec
                                  {0,6,4,4,10}, ζ_K(1)=23/15≈1.533
                                  (closest to ζ(2)≈1.645).  STRICT ∅-AXIOM.
  * `PiFiveGap.lean`            — π⁵ structural gap conjecture:
                                  1/(NS·NT·π⁵) ≈ 5446·10⁻⁷ matches
                                  observed gap 5443·10⁻⁷ within 3,
                                  vs α_GUT/45 within 40 — π⁵ form
                                  is ~13× closer.  Cohomology-graded
                                  motivation (Hodge pairing k=3,4).
                                  STRICT ∅-AXIOM rational checks.
  * `ProjectionRatios.lean`     — K_{3,2}^{(c=2)} ↔ Δ⁴ projection
                                  geometry: edge inventory (3 SS,
                                  6 ST, 1 TT), kernel (4), coverage
                                  ratio NS/d = 3/5 (= inverse of
                                  Y-norm 5/3), and structural origin
                                  of all 1/α_em integer coefficients
                                  (60, 30, 25, 4, 45) from c, NS,
                                  NT, d.  STRICT ∅-AXIOM.
  * `StructuralGap.lean`        — open 5.4×10⁻⁴ falsifier target

  Importing this single module pulls in the whole cluster.
-/
