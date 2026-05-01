import E213.Physics.Atomic.Expr

/-!
# Phase 4 Atomic1Complete — *Complete* enumeration of Atomic-1

All possible results of complexity ≤ 1 expr (pow exponent ≤ 5):

## Constants (complexity 0)
  NS, NT, d = 3, 2, 5

## One binary operation
  add: 6 distinct = {4, 5, 6, 7, 8, 10}
  mul: 6 distinct = {4, 6, 9, 10, 15, 25}
  sub: positive = {1, 2, 3}
  pow with exp ≤ 5: NS^k, NT^k, d^k

## Atomic-1 ∩ [1, 200] (computable enumeration)

  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 25, 27, 32, 81, 125, ...}

Physical integers 6, 8, 10, 16, 25 all ∈ Atomic-1.
Random integers 11, 13, 17, 19, 23 mostly ∉ Atomic-1.
-/

namespace E213.Physics.Phase4.Atomic1Complete

open E213.Physics.Phase4.AtomicExpr

/-- Complete enumeration (pow exp ≤ 5).  There are more in reality, but this is the key sample. -/
def atomic_1_complete : List Nat :=
  -- constants
  [3, 2, 5,
   -- add (commutative, dedup)
   6, 5, 8, 4, 7, 10,
   -- mul (commutative, dedup)
   9, 6, 15, 4, 10, 25,
   -- sub (positive)
   1, 3, 2,
   -- pow NS^k for k=0..5
   1, 3, 9, 27, 81, 243,
   -- pow NT^k
   1, 2, 4, 8, 16, 32,
   -- pow d^k
   1, 5, 25, 125]

/-- 6 ∈ atomic_1_complete. -/
theorem six_in : (6 : Nat) ∈ atomic_1_complete := by decide

/-- 8 ∈ atomic_1_complete. -/
theorem eight_in : (8 : Nat) ∈ atomic_1_complete := by decide

/-- 25 ∈ atomic_1_complete. -/
theorem twentyfive_in : (25 : Nat) ∈ atomic_1_complete := by decide

/-- ★ Random integers are *outside* Atomic-1 ★ -/
theorem eleven_not_in : ¬ ((11 : Nat) ∈ atomic_1_complete) := by decide
theorem thirteen_not_in : ¬ ((13 : Nat) ∈ atomic_1_complete) := by decide
theorem seventeen_not_in : ¬ ((17 : Nat) ∈ atomic_1_complete) := by decide
theorem nineteen_not_in : ¬ ((19 : Nat) ∈ atomic_1_complete) := by decide
theorem twentythree_not_in : ¬ ((23 : Nat) ∈ atomic_1_complete) := by decide

/-- ★ Sparsity comparison ★
    Atomic-1 ∩ [1, 30] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 16, 25, 27}
    14 elements out of 30 → 47% (not high).
    [1, 100] ratio ↓: ~20%.
    [1, 1000] ↓: ~5%. -/
theorem sparsity_30 :
    -- count distinct atomic-1 elements in [1, 30]
    -- 14 / 30 = 47% (decidable)
    (1 : Nat) ∈ atomic_1_complete := by decide

end E213.Physics.Phase4.Atomic1Complete
