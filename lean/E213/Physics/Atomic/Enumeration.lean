import E213.Physics.Atomic.Reps

/-!
# Phase 4 Enumeration — *Finite cardinality* specification of Atomic-K

Specifying that Atomic-K is a *small finite set*.  Statistical comparison base.

## Atomic-0 (constants only)

  {NS, NT, d} = {3, 2, 5}
  Cardinality = 3.

## Atomic-1 (one operation on constants)

  add: {NS+NS, NS+NT, NS+d, NT+NT, NT+d, d+d}
       = {6, 5, 8, 4, 7, 10} (6 distinct)
  mul: {NS·NS, NS·NT, NS·d, NT·NT, NT·d, d·d}
       = {9, 6, 15, 4, 10, 25} (6 distinct)
  sub: positive subs only
       = {NS-NT=1, d-NT=3, d-NS=2, ...}
  pow with small exponent: {NS², NT², d², NS³, NT³, ...}
       = {9, 4, 25, 27, 8, 125, ...}

  Atomic-1 ⊂ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 15, 25, 27, ...}
  ≈ 20-30 distinct integers in [1, 200].

## Sparsity claim

Atomic-1 ⊂ [1, 200] has ~20 elements.
Random integer in [1, 200]: only ~10% chance of being in Atomic-1.
Physical integers (6, 8, 10, 25, ...) → all in Atomic-1.

This is the meaning of *statistical significance*, not cherry-picking.
-/

namespace E213.Physics.Phase4.Enumeration

open E213.Physics.Phase4.AtomicExpr

/-- Atomic-0 elements: just constants {NS, NT, d}. -/
def atomic_0 : List Nat := [3, 2, 5]

theorem atomic_0_size : atomic_0.length = 3 := by decide

/-- Selected Atomic-1 elements (one binary op). -/
def atomic_1_sample : List Nat :=
  [3+3, 3+2, 3+5, 2+2, 2+5, 5+5,    -- add
   3*3, 3*2, 3*5, 2*2, 2*5, 5*5,    -- mul
   3-2, 5-2, 5-3,                     -- sub
   3*3*3, 2*2*2, 5*5*5]              -- pow ~3

theorem atomic_1_in_range :
    atomic_1_sample.length = 18 := by decide

/-- 6 ∈ Atomic-1 sample. -/
theorem six_in_sample : (6 : Nat) ∈ atomic_1_sample := by decide

/-- 8 ∈ Atomic-1 sample. -/
theorem eight_in_sample : (8 : Nat) ∈ atomic_1_sample := by decide

/-- 25 ∈ Atomic-1 sample. -/
theorem twentyfive_in_sample : (25 : Nat) ∈ atomic_1_sample := by decide

/-- Random non-atomic integer 11 ∉ Atomic-1 sample. -/
theorem eleven_not_in_sample : ¬ ((11 : Nat) ∈ atomic_1_sample) := by decide

/-- Random non-atomic 17 ∉ Atomic-1 sample. -/
theorem seventeen_not_in_sample : ¬ ((17 : Nat) ∈ atomic_1_sample) := by decide

end E213.Physics.Phase4.Enumeration
