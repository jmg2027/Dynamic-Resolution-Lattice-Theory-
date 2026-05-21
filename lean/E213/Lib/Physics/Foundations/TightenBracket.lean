import E213.Lib.Physics.Couplings.AlphaGUT

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

namespace E213.Lib.Physics.Foundations.TightenBracket

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound
open E213.Lib.Physics.Couplings.AlphaGUT

/-- ★ N=10 bracket on 1/α_GUT — explicit endpoints, inclusion of 41,
    exclusion of 42 / 41.30 / 41.25 / 38.70, width narrower than at N=3.
    All ∅-axiom decide. -/
theorem tighten_bracket_at_N10 :
    -- Explicit endpoints
    inv_lower 10 = (25 * 20407635072000, 13168189440000)
    ∧ inv_upper 10 = (25 * 217244540160000, 131681894400000)
    -- 41 ∈ bracket (confirms standard 1/α_GUT)
    ∧ (let lo := inv_lower 10
       let hi := inv_upper 10
       lo.1 < 41 * lo.2 ∧ 41 * hi.2 < hi.1)
    -- 42 ∉ bracket (excluded at N=10; was inside at N=3)
    ∧ (let hi := inv_upper 10
       hi.1 < 42 * hi.2)
    -- 41.30, 41.25 ∉ bracket (2-digit precision exclusions)
    ∧ (let hi := inv_upper 10
       100 * hi.1 < 4130 * hi.2)
    ∧ (let hi := inv_upper 10
       100 * hi.1 < 4125 * hi.2)
    -- 38.70 ∉ bracket from below
    ∧ (let lo := inv_lower 10
       387 * lo.2 < 10 * lo.1)
    -- N=10 strictly narrower than N=3
    ∧ (let lo3 := inv_lower 3; let hi3 := inv_upper 3
       let lo10 := inv_lower 10; let hi10 := inv_upper 10
       (hi3.1 * lo3.2 - lo3.1 * hi3.2) * hi10.2 * lo10.2
       > (hi10.1 * lo10.2 - lo10.1 * hi10.2) * hi3.2 * lo3.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Foundations.TightenBracket
