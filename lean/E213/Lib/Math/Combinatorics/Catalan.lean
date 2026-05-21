/-!
# Combinatorics — Catalan numbers (atomic table)

`C_n = (2n choose n) / (n+1)`, satisfying recursion
`C_(n+1) = Σ_{i=0..n} C_i · C_(n-i)`.

Atomic: provided as a finite table for n = 0..7 (covers all
practical dyadic-tree-shape counting on Δ⁴ ⊂ K_25).  The full
recursive `catalan : Nat → Nat` requires custom termination
witness; deferred.

Catalan numbers count:
  - dyadic-tree shapes with n internal nodes
  - balanced parenthesizations of n pairs
  - mountain ranges with n upsteps and n downsteps
  - non-crossing chord diagrams on 2n points
  All structurally native to 213's dyadic substrate.
-/

namespace E213.Lib.Math.Combinatorics.Catalan

/-- Catalan number table for n = 0..7, hand-verified. -/
def catalan : Nat → Nat
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | 5 => 42
  | 6 => 132
  | 7 => 429
  | _ + 8 => 0  -- out-of-table sentinel

/-- C₀ = 1 (rfl). -/
theorem catalan_0 : catalan 0 = 1 := rfl

/-- C₁ = 1. -/
theorem catalan_1 : catalan 1 = 1 := rfl

/-- C₂ = 2. -/
theorem catalan_2 : catalan 2 = 2 := rfl

/-- C₃ = 5. -/
theorem catalan_3 : catalan 3 = 5 := rfl

/-- C₄ = 14. -/
theorem catalan_4 : catalan 4 = 14 := rfl

/-- C₅ = 42 (★ the ubiquitous "fundamental Catalan count on the d=5 substrate" of combinatorics). -/
theorem catalan_5 : catalan 5 = 42 := rfl

/-- C₆ = 132. -/
theorem catalan_6 : catalan 6 = 132 := rfl

/-- C₇ = 429. -/
theorem catalan_7 : catalan 7 = 429 := rfl

/-- ★ **Catalan recursion check at n=2**: C₃ = C₀C₂ + C₁C₁ + C₂C₀
    = 1·2 + 1·1 + 2·1 = 5. ✓ -/
theorem catalan_recursion_3 :
    catalan 3 = catalan 0 * catalan 2 + catalan 1 * catalan 1
                + catalan 2 * catalan 0 := by decide

/-- Catalan recursion at n=3: C₄ = C₀C₃ + C₁C₂ + C₂C₁ + C₃C₀
    = 5 + 2 + 2 + 5 = 14. ✓ -/
theorem catalan_recursion_4 :
    catalan 4 = catalan 0 * catalan 3 + catalan 1 * catalan 2
                + catalan 2 * catalan 1 + catalan 3 * catalan 0 :=
  by decide

end E213.Lib.Math.Combinatorics.Catalan
