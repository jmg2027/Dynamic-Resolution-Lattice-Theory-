import E213.Term.Term

/-!
# E213.Term.Compare — decidable comparison over Term.

Returns Bool — bypasses Lean `decide` / `Decidable` typeclass.
All theorems via `rfl` or structural recursion → 0 axiom maintained.
-/

namespace E213.Term.Term

/-- Bool version of `a ≤ b` (based on Nat.ble). -/
protected def le_b (a b : Term) : Bool := Nat.ble (Term.eval a) (Term.eval b)

/-- Bool version of `a < b`. -/
protected def lt_b (a b : Term) : Bool := Nat.ble (Nat.succ (Term.eval a)) (Term.eval b)

end E213.Term.Term

namespace E213.Term.Compare

open Term

/-- n_T < n_S < d  (basic ordering of 213). -/
theorem nT_lt_nS : Term.lt_b Term.nT Term.nS = true := rfl
theorem nS_lt_d  : Term.lt_b Term.nS Term.d  = true := rfl

/-- n_T ≤ c  (in fact n_T = c, weaker form as ≤). -/
theorem nT_le_c : Term.le_b Term.nT Term.c = true := rfl

/-- d² ≥ 2 n_S²  (Argon closure fits inside d²). -/
theorem dsq_ge_2nSsq :
    Term.le_b (mul (succ (succ zero)) (mul Term.nS Term.nS)) (mul Term.d Term.d) = true := rfl

/-- 2 n_S³ ≤ d³  (Xe closure fits inside d³). -/
theorem two_nS_cube_le_d_cube :
    Term.le_b (mul (succ (succ zero)) (mul Term.nS (mul Term.nS Term.nS)))
         (mul Term.d (mul Term.d Term.d)) = true := rfl

/-- 2 n_S² < d² + 1  (strict, 18 < 26). -/
theorem two_nS_sq_lt_d_sq_plus_1 :
    Term.lt_b (mul (succ (succ zero)) (mul Term.nS Term.nS))
         (add (mul Term.d Term.d) (succ zero)) = true := rfl

end E213.Term.Compare

#print axioms E213.Term.Compare.nT_lt_nS
#print axioms E213.Term.Compare.nS_lt_d
#print axioms E213.Term.Compare.nT_le_c
#print axioms E213.Term.Compare.dsq_ge_2nSsq
#print axioms E213.Term.Compare.two_nS_cube_le_d_cube
#print axioms E213.Term.Compare.two_nS_sq_lt_d_sq_plus_1
