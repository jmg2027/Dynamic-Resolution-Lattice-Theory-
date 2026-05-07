import E213.Lib.Physics.AlphaEM.Augmented
import E213.Lib.Physics.AlphaEM.Bare
import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.AlphaEM.Capstone
import E213.Lib.Physics.AlphaEM.CupChannelInventory
import E213.Lib.Physics.AlphaEM.NUniverseCandidates
import E213.Lib.Physics.AlphaEM.StructuralGap

/-! Spec-as-code entry point for E213.Lib.Physics.AlphaEM.

  1/α_em derivation cluster — seven topical files:

  * `Augmented.lean`            — Dyson tail + SO(10) + Gram self-energy bracket
  * `Bare.lean`                 — atomic integers + lattice prefactors + 5-term
  * `Brackets.lean`             — bare/tight/V137 rational brackets
  * `Capstone.lean`             — unified-sum + simplicial decomp + master
  * `CupChannelInventory.lean`  — Δ⁴ cup-channel finite enumeration
                                  (Step A of finite α_em derivation):
                                  10 edge×edge channels, 80 total,
                                  785 cross-terms; 30 channels to
                                  triangle outputs matches 1/α_2 = 30
  * `NUniverseCandidates.lean`  — five candidates for N_U
  * `StructuralGap.lean`        — open 5.4×10⁻⁴ falsifier target

  Importing this single module pulls in all seven.
-/
