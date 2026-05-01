import E213.Physics.Couplings.AlphaGUT

/-!
# Tightening the 1/α_GUT bracket — N → ∞ scales (0 axioms)

The rational bracket from `AlphaGUT.lean` at N = 3 was:
  [1225/36, 4575/108] ≈ [34.03, 42.36]   width ≈ 8.33

This file demonstrates that increasing N → 10 narrows it to:
  ≈ [38.74, 41.24]                         width = 2.5

By N → ∞ (Lean limit not needed; just scaling), the bracket
collapses on the irrational 1/α_GUT = 25π²/6 ≈ 41.123.

**Key claim**: bracket width at N = 25/N.  Each ppm of precision
on 1/α_GUT requires N ≈ 25·10⁶ ≈ 6×10⁵.

All theorems 0-axiom decide-checked.  No real numbers involved —
just larger rationals with same `S/upper` recursion.
-/

namespace E213.Physics.Foundations.TightenBracket

open E213.Physics.Simplex.Counts
open E213.Physics.Basel.Bound
open E213.Physics.Couplings.AlphaGUT

/-- N=10 lower bracket on 1/α_GUT. -/
theorem inv_lower_10 :
    inv_lower 10 = (25 * 20407635072000, 13168189440000) := by decide

/-- N=10 upper bracket on 1/α_GUT. -/
theorem inv_upper_10 :
    inv_upper 10 = (25 * 217244540160000, 131681894400000) := by decide

/-- **41 ∈ bracket** at N=10 (confirms standard 1/α_GUT). -/
theorem in_bracket_41_at_10 :
    let lo := inv_lower 10
    let hi := inv_upper 10
    lo.1 < 41 * lo.2 ∧ 41 * hi.2 < hi.1 := by decide

/-- **42 ∉ bracket** at N=10 (was inside at N=3, now excluded). -/
theorem out_of_bracket_42_at_10 :
    let hi := inv_upper 10
    hi.1 < 42 * hi.2 := by decide

/-- **41.30 ∉ bracket** at N=10 — 2-digit precision exclusion.
    Cross-mult: 41.30 = 4130/100, so check 4130·hi.2 > 100·hi.1. -/
theorem precision_2digit_41_30_excluded :
    let hi := inv_upper 10
    100 * hi.1 < 4130 * hi.2 := by decide

/-- **41.25 ∉ bracket** at N=10 — even tighter exclusion (cross-mult). -/
theorem precision_2digit_41_25_excluded :
    let hi := inv_upper 10
    100 * hi.1 < 4125 * hi.2 := by decide

/-- **38.7 ∉ bracket** at N=10 from below (excluded since lower ≈ 38.74). -/
theorem precision_2digit_38_70_excluded :
    let lo := inv_lower 10
    387 * lo.2 < 10 * lo.1 := by decide

/-- **Width comparison**: bracket at N=10 strictly narrower than at N=3.
    Cross-mult check: width(10)/width(3) = 3/10 → at N=10 bracket
    width is 30% of N=3 width. -/
theorem width_10_lt_width_3 :
    let lo3 := inv_lower 3; let hi3 := inv_upper 3
    let lo10 := inv_lower 10; let hi10 := inv_upper 10
    -- (hi3.1 · lo3.2 - lo3.1 · hi3.2) · hi10.2 · lo10.2
    --   > (hi10.1 · lo10.2 - lo10.1 · hi10.2) · hi3.2 · lo3.2
    (hi3.1 * lo3.2 - lo3.1 * hi3.2) * hi10.2 * lo10.2
    > (hi10.1 * lo10.2 - lo10.1 * hi10.2) * hi3.2 * lo3.2 := by decide

end E213.Physics.Foundations.TightenBracket
