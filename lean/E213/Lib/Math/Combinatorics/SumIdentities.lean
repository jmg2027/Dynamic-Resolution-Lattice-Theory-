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

/-- ★★ **Nicomachus' theorem**: `(Σ_{i≤n} i)² = Σ_{i≤n} i³` — the sum of cubes is the square
    of the triangular number.  Division-free form `(2·Σ i)² = 4·Σ i³`. -/
theorem nicomachus : ∀ n,
    (2 * sumTo (n + 1) (fun i => i)) * (2 * sumTo (n + 1) (fun i => i))
      = 4 * sumTo (n + 1) (fun i => i * i * i)
  | 0     => rfl
  | n + 1 => by
      have ih := nicomachus n
      have htri := two_sumTo_id n
      have key : 2 * (sumTo (n + 1) (fun i => i) + (n + 1)) = n * (n + 1) + 2 * (n + 1) := by
        rw [Nat.mul_add, htri]
      show (2 * (sumTo (n + 1) (fun i => i) + (n + 1)))
            * (2 * (sumTo (n + 1) (fun i => i) + (n + 1)))
          = 4 * (sumTo (n + 1) (fun i => i * i * i) + (n + 1) * (n + 1) * (n + 1))
      rw [key, Nat.mul_add 4 (sumTo (n + 1) (fun i => i * i * i)) ((n + 1) * (n + 1) * (n + 1)),
          ← ih, htri]
      ring_nat

/-- ★★ **Sum of the first `n` squares**: `6·Σ_{i≤n} i² = n(n+1)(2n+1)` (division-free). -/
theorem six_sumTo_sq : ∀ n, 6 * sumTo (n + 1) (fun i => i * i) = n * (n + 1) * (2 * n + 1)
  | 0     => rfl
  | n + 1 => by
      show 6 * (sumTo (n + 1) (fun i => i * i) + (n + 1) * (n + 1))
          = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
      rw [Nat.mul_add, six_sumTo_sq n]; ring_nat

end E213.Lib.Math.Combinatorics.SumIdentities
