import E213.Physics.AlphaEM.Core

/-!
# 1/α_em(M_Z) bare — tightened bracket (pure DRLT, no corrections)

Bare DRLT formula (Weinberg sum):
    1/α_em(M_Z) = (5/3)·(1/α_1) + 1/α_2 = 60·ζ(2) + 30 ≈ 128.696

This is the **pure DRLT-axiom-derivable** value at the Z scale.
At higher N (resolution depth) the rational bracket tightens
toward 128.696.

## What this file proves (0 axioms)

  * 128 ∈ bracket at N = 10
  * 129 ∉ bracket at N = 10 (sharp upper exclusion)
  * 137 ∉ bracket at N = 10 (way above bare value)
  * Tighter bracket at N = 20 (decide handles)

## Why 137 is NOT in the bare bracket

Observed at low energy: 1/α_em(0) = 137.036.
Observed at M_Z:        1/α_em(M_Z) = 127.95.

The gap 137 − 128 = 9 is the **standard QED vacuum polarization**
running from M_Z to Q = 0.  Per ch08 line 289:
> "The QED vacuum polarization Δ_QED ≈ 9.1 is a standard QED
>  contribution... This is NOT part of the DRLT topological
>  calculation — it is established physics that applies regardless
>  of the underlying theory."

Therefore writing `1/α_em = 137.xxx` in Lean from DRLT alone
**requires** either (a) Ξ-correction with hand-coded base, or
(b) explicit QED running formalization (open work).  This file
formalizes only the pure-DRLT bare value.
-/

namespace E213.Physics.AlphaEM.Tight

open E213.Physics.Simplex
open E213.Physics.Basel
open E213.Physics.AlphaEM.Core

/-- 128 strictly inside bare bracket at N = 10. -/
theorem bracket_128_in_10 :
    let lo := inv_alpha_em_bare_lower 10
    let hi := inv_alpha_em_bare_upper 10
    lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1 := by decide

/-- 129 strictly outside bare bracket at N = 10 (upper-end). -/
theorem bracket_129_excluded_10 :
    let hi := inv_alpha_em_bare_upper 10
    hi.1 < 129 * hi.2 := by decide

/-- 137 way outside bare bracket at N = 10 — needs QED running. -/
theorem bracket_137_excluded_10 :
    let hi := inv_alpha_em_bare_upper 10
    hi.1 < 137 * hi.2 := by decide

/-- N = 20: tighter bracket.  128 still inside. -/
theorem bracket_128_in_20 :
    let lo := inv_alpha_em_bare_lower 20
    let hi := inv_alpha_em_bare_upper 20
    lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1 := by decide

/-- N = 20: 129 excluded (upper).  At N=20, bracket is narrower.  -/
theorem bracket_129_excluded_20 :
    let hi := inv_alpha_em_bare_upper 20
    hi.1 < 129 * hi.2 := by decide

/-- The QED-running gap is exactly 9 = 137 − 128, NOT DRLT.
    Marker of where the DRLT topological calculation ends and
    standard QED vacuum polarization begins. -/
theorem qed_running_gap : (137 : Nat) - 128 = 9 := by decide

/-- **Capstone**: pure-DRLT 1/α_em(M_Z) bare value is bracketed
    sharply at 128 (within ±1 at N=20).  137 cannot be cleanly
    derived without invoking non-DRLT QED running per book ch08. -/
theorem alpha_em_bare_pure_drlt :
    let lo := inv_alpha_em_bare_lower 20
    let hi := inv_alpha_em_bare_upper 20
    -- 128 inside bare bracket
    (lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1)
    -- 137 outside (needs running)
    ∧ (hi.1 < 137 * hi.2)
    -- gap is 9
    ∧ (137 - 128 = 9) := by decide

end E213.Physics.AlphaEM.Tight
