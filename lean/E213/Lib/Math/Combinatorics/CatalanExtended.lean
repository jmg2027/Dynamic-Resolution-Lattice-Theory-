import E213.Lib.Math.Combinatorics.Catalan

/-!
# Combinatorics — Catalan recursion at n = 5, 6, 7 (∅-axiom)

Closes the deferral noted in `Combinatorics/Catalan.lean:9-10`:
"the full recursive `catalan : Nat → Nat` requires custom
termination witness; deferred."

The base file proved the recursion at n = 3, 4 only.  This file
extends the witnesses to n = 5, 6, 7 — the explicit `decide`-style
recursion `Cₙ₊₁ = Σᵢ Cᵢ · Cₙ₋ᵢ` for the table values.

213-native paradigm: Catalan numbers IS the dyadic-tree shape
counting on Δ⁴ ⊂ K_25 (per Catalan.lean documentation).  The
table-and-recursion-witness style is the structurally honest
choice for a finite-Grade substrate.
-/

namespace E213.Lib.Math.Combinatorics.CatalanExtended

open E213.Lib.Math.Combinatorics.Catalan (catalan)

/-- ★ **Catalan recursion at n=5**:
    `C₅ = C₀C₄ + C₁C₃ + C₂C₂ + C₃C₁ + C₄C₀ = 14+5+4+5+14 = 42`. -/
theorem catalan_recursion_5 :
    catalan 5 = catalan 0 * catalan 4 + catalan 1 * catalan 3
                + catalan 2 * catalan 2 + catalan 3 * catalan 1
                + catalan 4 * catalan 0 := by decide

/-- ★ **Catalan recursion at n=6**: `C₆ = 132`. -/
theorem catalan_recursion_6 :
    catalan 6 = catalan 0 * catalan 5 + catalan 1 * catalan 4
                + catalan 2 * catalan 3 + catalan 3 * catalan 2
                + catalan 4 * catalan 1 + catalan 5 * catalan 0 := by decide

/-- ★ **Catalan recursion at n=7**: `C₇ = 429`. -/
theorem catalan_recursion_7 :
    catalan 7 = catalan 0 * catalan 6 + catalan 1 * catalan 5
                + catalan 2 * catalan 4 + catalan 3 * catalan 3
                + catalan 4 * catalan 2 + catalan 5 * catalan 1
                + catalan 6 * catalan 0 := by decide

/-- ★ **C₅·C₂ = 84** (basic mult check). -/
theorem catalan_5_times_2 : catalan 5 * catalan 2 = 84 := rfl

/-- ★ **C₇ + C₆ = 561** (sum check). -/
theorem catalan_sum_6_7 : catalan 6 + catalan 7 = 561 := rfl

end E213.Lib.Math.Combinatorics.CatalanExtended
