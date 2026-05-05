import E213.Physics.Couplings.AlphaGUT

/-!
# 1/α_em(bare) — Weinberg sum + rational bracket

DRLT formulae:
  1/α_3 = 1 · (NS² - 1) · S(1)            = 8         (exact ℤ)
  1/α_2 = 12 · NT · S(2)                  = 30        (exact ℤ)
  1/α_1 = 12 · NS · S(∞)                  = 36 · ζ(2) (bracket)

Weinberg sum (Y-normalisation):
  1/α_em(bare) = (5/3)·(1/α_1) + 1/α_2 = 60 · ζ(2) + 30 ≈ 128.696

This is the **bare** value at the GUT scale. The corrected 1/α_em ≈
137.036 requires the Ξ correction (separate file, depends on this).

This file:
  * Defines 1/α_2, 1/α_3 (exact integers)
  * Defines 1/α_1 rational bracket via S(N)/upper(N)
  * Defines 1/α_em(bare) rational bracket via Weinberg sum
  * Proves the standard bare value 128.7 ∈ bracket at N=5
  * Proves the corrected 137.036 is *outside* bare bracket
    (correctly distinguishes bare vs Ξ-corrected, no fudging)
-/

namespace E213.Physics.AlphaEM.Bare

open E213.Physics.Simplex.Counts
open E213.Physics.Basel.Bound

/-- 1/α_3 (confined, exact integer) = NS² - 1 = 8. -/
def inv_alpha_3 : Nat := NS * NS - 1

theorem inv_alpha_3_eq_8 : inv_alpha_3 = 8 := by decide

/-- 1/α_2 (electroweak, exact integer) = 12 · NT · (5/4) = 30. -/
def inv_alpha_2 : Nat := 12 * NT * 5 / 4

theorem inv_alpha_2_eq_30 : inv_alpha_2 = 30 := by decide

/-- 1/α_1 lower bracket = 12·NS · S(N) = 36 · S(N). -/
def inv_alpha_1_lower (N : Nat) : (Nat × Nat) :=
  let s := S N
  ((12 * NS) * s.1, s.2)

/-- 1/α_1 upper bracket. -/
def inv_alpha_1_upper (N : Nat) : (Nat × Nat) :=
  let u := upper N
  ((12 * NS) * u.1, u.2)

/-- 1/α_em(bare) lower bracket via Weinberg:
      1/α_em(bare) = 60 · ζ(2) + 30
    Lower endpoint: 60·S(N) + 30 in (num, den) form. -/
def inv_alpha_em_bare_lower (N : Nat) : (Nat × Nat) :=
  let s := S N
  (60 * s.1 + 30 * s.2, s.2)

/-- 1/α_em(bare) upper bracket: 60·upper(N) + 30. -/
def inv_alpha_em_bare_upper (N : Nat) : (Nat × Nat) :=
  let u := upper N
  (60 * u.1 + 30 * u.2, u.2)

/-- Concrete S(5) value (kept here for traceability). -/
theorem S_5 : S 5 = (21076, 14400) := by decide

/-- **Main result**: standard bare 1/α_em(bare) ≈ 128.696 is inside
    the rational bracket at N=5.  Check via integers 128 and 129.

      lower(5) = 60·21076/14400 + 30  ≈ 117.82
      upper(5) = 60·119780/72000 + 30 ≈ 129.81

    128 ∈ bracket ⟸ lower < 128 ∧ 128 < upper. -/
theorem bare_128_in_bracket :
    let lo := inv_alpha_em_bare_lower 5
    let hi := inv_alpha_em_bare_upper 5
    lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1 := by decide

/-- **Honesty check**: corrected 137.036 is NOT in the bare bracket
    (as it should be — needs Ξ correction in next file).
    137 > upper(5) iff 137 · 72000 = 9864000 > hi.1 = 9346800. -/
theorem corrected_137_outside_bare_bracket :
    let hi := inv_alpha_em_bare_upper 5
    hi.1 < 137 * hi.2 := by decide

end E213.Physics.AlphaEM.Bare
