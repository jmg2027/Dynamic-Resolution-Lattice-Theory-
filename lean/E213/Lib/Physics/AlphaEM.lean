import E213.Lib.Physics.AlphaEM.Augmented
import E213.Lib.Physics.AlphaEM.Bare
import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.AlphaEM.Capstone
import E213.Lib.Physics.AlphaEM.CupChannelInventory
import E213.Lib.Physics.AlphaEM.CupRingTrace
import E213.Lib.Physics.AlphaEM.LaplacianSpectrum
import E213.Lib.Physics.AlphaEM.NUniverseCandidates
import E213.Lib.Physics.AlphaEM.ProjectionRatios
import E213.Lib.Physics.AlphaEM.StructuralGap

/-! Spec-as-code entry point for E213.Lib.Physics.AlphaEM.

  1/α_em derivation cluster — ten topical files:

  * `Augmented.lean`            — Dyson tail + SO(10) + Gram self-energy bracket
  * `Bare.lean`                 — atomic integers + lattice prefactors + 5-term
  * `Brackets.lean`             — bare/tight/V137 rational brackets
  * `Capstone.lean`             — unified-sum + simplicial decomp + master
  * `CupChannelInventory.lean`  — Δ⁴ cup-channel finite enumeration
                                  (Step A): 10 / 80 / 785 channels
  * `CupRingTrace.lean`         — bottom-up cup-ring functional tests
                                  (Test 1): F₁..F₅ — none give 137,
                                  pointing to Laplacian or N_U
  * `LaplacianSpectrum.lean`    — finite ζ-analog via cochain Laplacian
                                  (Test 2): Δ⁴ rank=30 uniform ev=5,
                                  ζ_Δ(2)=6/5; K_{3,2}^{(c=2)} spec
                                  {0,6,4,4,10}, ζ_K(1)=23/15≈1.533
                                  (closest to ζ(2)≈1.645).  STRICT ∅-AXIOM.
  * `NUniverseCandidates.lean`  — five candidates for N_U
  * `ProjectionRatios.lean`     — K_{3,2}^{(c=2)} ↔ Δ⁴ projection
                                  geometry: edge inventory (3 SS,
                                  6 ST, 1 TT), kernel (4), coverage
                                  ratio NS/d = 3/5 (= inverse of
                                  Y-norm 5/3), and structural origin
                                  of all 1/α_em integer coefficients
                                  (60, 30, 25, 4, 45) from c, NS,
                                  NT, d.  STRICT ∅-AXIOM.
  * `StructuralGap.lean`        — open 5.4×10⁻⁴ falsifier target

  Importing this single module pulls in all ten.
-/
