import E213.Lib.Physics.AlphaEM.Augmented
import E213.Lib.Physics.AlphaEM.Bare
import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.AlphaEM.Capstone
import E213.Lib.Physics.AlphaEM.CupChannelInventory
import E213.Lib.Physics.AlphaEM.CupRingTrace
import E213.Lib.Physics.AlphaEM.NUniverseCandidates
import E213.Lib.Physics.AlphaEM.StructuralGap

/-! Spec-as-code entry point for E213.Lib.Physics.AlphaEM.

  1/α_em derivation cluster — eight topical files:

  * `Augmented.lean`            — Dyson tail + SO(10) + Gram self-energy bracket
  * `Bare.lean`                 — atomic integers + lattice prefactors + 5-term
  * `Brackets.lean`             — bare/tight/V137 rational brackets
  * `Capstone.lean`             — unified-sum + simplicial decomp + master
  * `CupChannelInventory.lean`  — Δ⁴ cup-channel finite enumeration
                                  (Step A): 10 / 80 / 785 channels
  * `CupRingTrace.lean`         — bottom-up cup-ring functional tests
                                  (Test 1 of pure-derivation conjecture):
                                  F₁=F₂=4, F₃=80, F₄=240, F₅=120 — none
                                  give 137; gap analysis points to
                                  Laplacian-spectrum or N_U-resolution
                                  candidates as next direction
  * `NUniverseCandidates.lean`  — five candidates for N_U
  * `StructuralGap.lean`        — open 5.4×10⁻⁴ falsifier target

  Importing this single module pulls in all eight.
-/
