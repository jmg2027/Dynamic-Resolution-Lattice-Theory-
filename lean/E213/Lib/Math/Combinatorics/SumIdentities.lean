import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# SumIdentities — elementary figurate-number identities (∅-axiom)

Pure-`Nat` closed forms for the basic finite sums, division-free.

  * `sumTo_odds` : `Σ_{i<n} (2i+1) = n²` (the sum of the first `n` odd numbers).
  * `two_sumTo_id` : `2·Σ_{i≤n} i = n(n+1)` (triangular numbers, division-free).

All zero-axiom.
-/

namespace E213.Lib.Math.Combinatorics.SumIdentities

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- ★ **Sum of the first `n` odd numbers is `n²`**: `Σ_{i<n} (2i+1) = n²`. -/
theorem sumTo_odds : ∀ n, sumTo n (fun i => 2 * i + 1) = n * n
  | 0     => rfl
  | n + 1 => by
      show sumTo n (fun i => 2 * i + 1) + (2 * n + 1) = (n + 1) * (n + 1)
      rw [sumTo_odds n]; ring_nat

/-- ★ **Triangular numbers** (division-free): `2·Σ_{i≤n} i = n(n+1)`. -/
theorem two_sumTo_id : ∀ n, 2 * sumTo (n + 1) (fun i => i) = n * (n + 1)
  | 0     => rfl
  | n + 1 => by
      show 2 * (sumTo (n + 1) (fun i => i) + (n + 1)) = (n + 1) * (n + 1 + 1)
      rw [Nat.mul_add, two_sumTo_id n]; ring_nat

end E213.Lib.Math.Combinatorics.SumIdentities
