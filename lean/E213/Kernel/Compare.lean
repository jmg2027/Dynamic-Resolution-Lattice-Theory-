import E213.Kernel.Term

/-!
# E213.Kernel.Compare — decidable comparison over Term.

Returns Bool — bypasses Lean `decide` / `Decidable` typeclass.
All theorems via `rfl` or structural recursion → 0 axiom maintained.
-/

namespace E213.Kernel.Term

/-- Bool version of `a ≤ b` (based on Nat.ble). -/
def le_b (a b : Term) : Bool := Nat.ble (eval a) (eval b)

/-- Bool version of `a < b`. -/
def lt_b (a b : Term) : Bool := Nat.ble (Nat.succ (eval a)) (eval b)

end E213.Kernel.Term

namespace E213.Kernel.Compare

open Term

/-- n_T < n_S < d  (basic ordering of 213). -/
theorem nT_lt_nS : lt_b nT nS = true := rfl
theorem nS_lt_d  : lt_b nS d  = true := rfl

/-- n_T ≤ c  (in fact n_T = c, weaker form as ≤). -/
theorem nT_le_c : le_b nT c = true := rfl

/-- d² ≥ 2 n_S²  (Argon closure fits inside d²). -/
theorem dsq_ge_2nSsq :
    le_b (mul (succ (succ zero)) (mul nS nS)) (mul d d) = true := rfl

/-- 2 n_S³ ≤ d³  (Xe closure fits inside d³). -/
theorem two_nS_cube_le_d_cube :
    le_b (mul (succ (succ zero)) (mul nS (mul nS nS)))
         (mul d (mul d d)) = true := rfl

/-- 2 n_S² < d² + 1  (strict, 18 < 26). -/
theorem two_nS_sq_lt_d_sq_plus_1 :
    lt_b (mul (succ (succ zero)) (mul nS nS))
         (add (mul d d) (succ zero)) = true := rfl

end E213.Kernel.Compare

#print axioms E213.Kernel.Compare.nT_lt_nS
#print axioms E213.Kernel.Compare.nS_lt_d
#print axioms E213.Kernel.Compare.nT_le_c
#print axioms E213.Kernel.Compare.dsq_ge_2nSsq
#print axioms E213.Kernel.Compare.two_nS_cube_le_d_cube
#print axioms E213.Kernel.Compare.two_nS_sq_lt_d_sq_plus_1
