import E213.Lib.Physics.AlphaEM.Augmented
import E213.Lib.Physics.AlphaEM.Bare
import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.AlphaEM.Capstone
import E213.Lib.Physics.AlphaEM.NUniverseCandidates
import E213.Lib.Physics.AlphaEM.StructuralGap

/-! Spec-as-code entry point for E213.Lib.Physics.AlphaEM.

  1/α_em derivation cluster — six topical files (sorted ls = topic index):

  * `Augmented.lean`        — Dyson tail + SO(10) + Gram self-energy bracket
  * `Bare.lean`             — atomic integers + lattice prefactors + 5-term
  * `Brackets.lean`         — bare/tight/V137 rational brackets
  * `Capstone.lean`         — unified-sum + simplicial decomp + master + milestone
  * `NUniverseCandidates.lean` — five candidates for N_U
  * `StructuralGap.lean`    — open 5.4×10⁻⁴ falsifier target

  Importing this single module pulls in all six.
-/
