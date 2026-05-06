import E213.Term.Term

/-!
# E213.Term.Decide — finite-enumeration decision procedures.

Lean's `decide` tactic often pulls in `Decidable` typeclass + Classical.
For a finite discrete lattice, *pure Bool functions + finite recursion* are
sufficient → bypassing the typeclass.

  allBelow n p   = ∀ x < n, p x = true   (Bool)
  existsBelow n p = ∃ x < n, p x = true  (Bool)

All use structural induction + Bool operations → 0 axiom.
-/

namespace E213.Term.Decide

/-- Bool version of ∀ x < n, p x. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0,     _ => true
  | n+1,   p => (allBelow n p) && p n

/-- Bool version of ∃ x < n, p x. -/
def existsBelow : Nat → (Nat → Bool) → Bool
  | 0,     _ => false
  | n+1,   p => (existsBelow n p) || p n

end E213.Term.Decide

namespace E213.Term.Decide.Tests

/-- All numbers less than d (= 5) are ≤ 4. -/
theorem all_lt_d_le_4 :
    allBelow 5 (fun x => Nat.ble x 4) = true := rfl

/-- 4 exists among numbers less than d. -/
theorem exists_lt_d_eq_4 :
    existsBelow 5 (fun x => Nat.beq x 4) = true := rfl

/-- 5 is absent among numbers less than d. -/
theorem no_lt_d_eq_5 :
    existsBelow 5 (fun x => Nat.beq x 5) = false := rfl

/-- For all pairs (i, j) with i, j < 25, we have i + j ≤ 48.
    (Light sanity check — sum bound within the d² lattice). -/
theorem pair_sum_bound :
    allBelow 25 (fun i =>
      allBelow 25 (fun j => Nat.ble (i + j) 48)) = true := rfl

/-- magic numbers (2, 8, 20, 28, 50, 82, 126) are all ≤ 126. -/
theorem magic_le_126 :
    [2, 8, 20, 28, 50, 82, 126].all (fun n => Nat.ble n 126) = true := rfl

/-- magic numbers are all even. -/
theorem magic_all_even :
    [2, 8, 20, 28, 50, 82, 126].all (fun n => Nat.beq (n % 2) 0) = true := rfl

end E213.Term.Decide.Tests

#print axioms E213.Term.Decide.Tests.all_lt_d_le_4
#print axioms E213.Term.Decide.Tests.exists_lt_d_eq_4
#print axioms E213.Term.Decide.Tests.no_lt_d_eq_5
#print axioms E213.Term.Decide.Tests.pair_sum_bound
#print axioms E213.Term.Decide.Tests.magic_le_126
#print axioms E213.Term.Decide.Tests.magic_all_even
