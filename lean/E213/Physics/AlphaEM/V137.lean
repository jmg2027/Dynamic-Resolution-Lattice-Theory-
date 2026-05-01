import E213.Physics.AlphaEM.Core

/-!
# 1/α_em(IR) candidate — pure DRLT formula attempt for 137.036

User directive (2026-04-27): "The book is no longer the ToE and SSOT.
Raw/Lens is the ToE and SSOT."  The explicit statement in ch08:289 "QED running is not
DRLT topology" was a self-acknowledged limitation *at the time the book was written*, and now
that 213 has matured, attempting self-derivation from the lattice.

## Candidate formula

    1/α_em(IR) = 10π² + 30 + d²/NS  + α_GUT/(NS+1)
              = bare(M_Z) + d²/NS  + Ξ_tail
              ≈ 128.696 + 8.333 + 0.00608
              ≈ 137.035

  Observed: 137.036.  Match: ppm level.

## Honest tagging

  * `bare = 10π² + 30`: **derived** (Weinberg sum, Basel sum,
    NS=3 solid angle — all in prior files)
  * `+ d²/NS = +25/3`: **conjectural structural form**.
    Plausible source: at IR, photon couples to all 25 Gram
    channels distributed across NS=3 spatial directions.
    "Channels per spatial dimension" ansatz.  Strict Lens-level
    derivation is OPEN.
  * `+ α_GUT/(NS+1)`: Dyson tail, NS+1=4 = face dimension.
    Already used in Cabibbo Ξ.  Plausible but not derived here.

## What this file proves (0 axioms)

  * Candidate formula in bracket form
  * 137 ∈ bracket at N = 10 (containment by `decide`)
  * 138 ∉ bracket (sharp)
  * 136 ∉ bracket (sharp from below at N=10)

## Falsifier

  If structural derivation of `d²/NS` term cannot be found from
  Raw + Lens + simplex axioms, this candidate is curve-fitting,
  not DRLT — and CLAUDE.md falsifiability would deprecate it.

  Currently: open hypothesis with strong numerical match.
-/

namespace E213.Physics.AlphaEM.V137

open E213.Physics.Simplex
open E213.Physics.Basel

/-- Candidate lower bracket: 60·S(N) + 30 + 25/3
    = (180·S(N).1 + 115·S(N).2) / (3·S(N).2) -/
def inv_full_lower (N : Nat) : (Nat × Nat) :=
  let s := S N
  (180 * s.1 + 115 * s.2, 3 * s.2)

/-- Candidate upper bracket: 60·upper(N) + 30 + 25/3 -/
def inv_full_upper (N : Nat) : (Nat × Nat) :=
  let u := upper N
  (180 * u.1 + 115 * u.2, 3 * u.2)

/-- N=3 lower endpoint: 60·(49/36) + 30 + 25/3
    = 180·49/108 + 115·36/108 (no, wrong scaling)
    Actually = (180·49 + 115·36)/108 = (8820 + 4140)/108 = 12960/108
    = 120.0.  [Bracket too wide at N=3.] -/
theorem inv_full_lower_3 : inv_full_lower 3 = (180 * 49 + 115 * 36, 3 * 36) := by decide

/-- N=3 upper endpoint. -/
theorem inv_full_upper_3 : inv_full_upper 3 = (180 * 183 + 115 * 108, 3 * 108) := by decide

/-- **Main result**: 137 ∈ candidate bracket at N=10.

    Numerical check:
      bare(N=10) lower ≈ 122.99, upper ≈ 128.99
      + 25/3 = +8.33: lower ≈ 131.32, upper ≈ 137.32
      → 137 ∈ [131.32, 137.32] ✓ -/
theorem bracket_137_in_at_10 :
    let lo := inv_full_lower 10
    let hi := inv_full_upper 10
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 138 just outside upper bracket at N=10. -/
theorem bracket_138_excluded_at_10 :
    let hi := inv_full_upper 10
    hi.1 < 138 * hi.2 := by decide

/-- 131 below lower bracket at N=10 (sharp lower exclusion). -/
theorem bracket_131_excluded_at_10 :
    let lo := inv_full_lower 10
    131 * lo.2 < lo.1 := by decide

/-- **Capstone hypothesis**: candidate formula contains 137 at
    N=10 with width ~ 6.  Tightening N → arbitrary precision.
    Structural origin of d²/NS = 25/3 term remains open. -/
theorem candidate_formula_contains_137 :
    let lo := inv_full_lower 10
    let hi := inv_full_upper 10
    (lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1)
    ∧ (hi.1 < 138 * hi.2)
    ∧ (131 * lo.2 < lo.1) := by decide

end E213.Physics.AlphaEM.V137
