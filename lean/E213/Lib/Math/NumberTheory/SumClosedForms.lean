import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# Closed forms for power sums (∅-axiom)

The triangular and square-pyramidal closed forms, stated multiplier-cleared over `Nat` to
avoid division: `2·Σ_{k<n}(k+1) = n(n+1)` and `6·Σ_{k<n}(k+1)² = n(n+1)(2n+1)`.  Genuine
polynomial summation (companion to the geometric `geom_sum`), by induction + `ring_nat`.
-/

namespace E213.Lib.Math.NumberTheory.SumClosedForms

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- ★ **Triangular number closed form**: `2·Σ_{k=1}^{n} k = n(n+1)` (cleared form). -/
theorem two_mul_sum_first : ∀ n, 2 * sumTo n (fun k => k + 1) = n * (n + 1)
  | 0 => by decide
  | n + 1 => by
      rw [sumTo_succ,
          show 2 * (sumTo n (fun k => k + 1) + (n + 1))
            = 2 * sumTo n (fun k => k + 1) + 2 * (n + 1) from by ring_nat,
          two_mul_sum_first n]
      ring_nat

/-- ★ **Square-pyramidal closed form**: `6·Σ_{k=1}^{n} k² = n(n+1)(2n+1)` (cleared form). -/
theorem six_mul_sum_sq_first : ∀ n,
    6 * sumTo n (fun k => (k + 1) * (k + 1)) = n * (n + 1) * (2 * n + 1)
  | 0 => by decide
  | n + 1 => by
      rw [sumTo_succ,
          show 6 * (sumTo n (fun k => (k + 1) * (k + 1)) + (n + 1) * (n + 1))
            = 6 * sumTo n (fun k => (k + 1) * (k + 1)) + 6 * ((n + 1) * (n + 1)) from by ring_nat,
          six_mul_sum_sq_first n]
      ring_nat

end E213.Lib.Math.NumberTheory.SumClosedForms
