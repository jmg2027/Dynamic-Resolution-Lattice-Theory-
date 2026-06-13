import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic

/-!
# Lib.Math.NumberTheory.ChebyshevLower — the Chebyshev lower bound `π(N) ≥ c·N/ln N`

The matching direction to the density cut (`MultSystemValue.primeDensityToZero`).
Route: `2^n ≤ C(2n,n) ≤ (2n)^{π(2n)}`, so `n ≤ π(2n)·log₂(2n)`.

This file builds the **Kummer prime-power bound** `vp_p(C(2n,n)) ≤ ⌊log_p(2n)⌋`
(via Legendre's formula `vp_p(m!) = Σ ⌊m/p^i⌋` and the per-term floor inequality
`⌊2n/d⌋ ≤ 2⌊n/d⌋ + [d ≤ 2n]`), then `C(2n,n) ≤ (2n)^{π(2n)}` and the lower bound.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ChebyshevLower

open E213.Meta.Nat.NatDiv213 (div_add_mod_pure add_mul_div_left_pure div_lt_of_lt_mul)

/-- **The per-term Kummer inequality**: `⌊2n/d⌋ ≤ 2⌊n/d⌋ + [d ≤ 2n]` (`d > 0`).
    For `d ≤ 2n`: `⌊2n/d⌋ ≤ 2⌊n/d⌋ + 1` (the floor of a doubled quotient gains at
    most one).  For `d > 2n`: `⌊2n/d⌋ = 0`.  The heart of Kummer's bound on
    `vp_p(C(2n,n))`. -/
theorem floor_two_mul_div_le (n d : Nat) (hd : 0 < d) :
    2 * n / d ≤ 2 * (n / d) + (if d ≤ 2 * n then 1 else 0) := by
  by_cases h : d ≤ 2 * n
  · rw [if_pos h]
    have hdm : d * (n / d) + n % d = n := div_add_mod_pure n d
    have h2n : 2 * n = 2 * (n % d) + d * (2 * (n / d)) := by
      have hexp : 2 * (d * (n / d) + n % d) = 2 * (n % d) + d * (2 * (n / d)) := by ring_nat
      rwa [hdm] at hexp
    have hkey : 2 * n / d = 2 * (n / d) + 2 * (n % d) / d := by
      rw [h2n, add_mul_div_left_pure (2 * (n % d)) d (2 * (n / d)) hd]
      exact Nat.add_comm _ _
    have hmodlt : 2 * (n % d) < d * 2 := by
      have hlt : n % d < d := Nat.mod_lt n hd
      calc 2 * (n % d) < 2 * (n % d) + 2 := Nat.lt_add_of_pos_right (by decide)
        _ = 2 * (n % d + 1) := by ring_nat
        _ ≤ 2 * d := Nat.mul_le_mul (Nat.le_refl 2) hlt
        _ = d * 2 := by ring_nat
    have hmod1 : 2 * (n % d) / d ≤ 1 := Nat.le_of_lt_succ (div_lt_of_lt_mul hmodlt)
    rw [hkey]; exact Nat.add_le_add (Nat.le_refl _) hmod1
  · rw [if_neg h, Nat.add_zero, Nat.div_eq_of_lt (Nat.not_le.mp h)]
    exact Nat.zero_le _

end E213.Lib.Math.NumberTheory.ChebyshevLower
