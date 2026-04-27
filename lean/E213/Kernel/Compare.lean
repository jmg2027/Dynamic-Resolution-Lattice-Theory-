import E213.Kernel.Term

/-!
# E213.Kernel.Compare — Term 위의 결정 가능 비교.

Bool 반환 — Lean `decide` / `Decidable` typeclass 우회.
모든 정리 `rfl` 또는 구조귀납 → 0 axiom 유지.
-/

namespace E213.Kernel.Term

/-- `a ≤ b` 의 Bool 버전 (Nat.ble 기반). -/
def le_b (a b : Term) : Bool := Nat.ble (eval a) (eval b)

/-- `a < b` 의 Bool 버전. -/
def lt_b (a b : Term) : Bool := Nat.ble (Nat.succ (eval a)) (eval b)

end E213.Kernel.Term

namespace E213.Kernel.Compare

open Term

/-- n_T < n_S < d  (213 의 기본 ordering). -/
theorem nT_lt_nS : lt_b nT nS = true := rfl
theorem nS_lt_d  : lt_b nS d  = true := rfl

/-- n_T ≤ c  (사실 n_T = c, ≤ 형태로 weaker form). -/
theorem nT_le_c : le_b nT c = true := rfl

/-- d² ≥ 2 n_S²  (Argon 닫힘이 d² 안에 들어감). -/
theorem dsq_ge_2nSsq :
    le_b (mul (succ (succ zero)) (mul nS nS)) (mul d d) = true := rfl

/-- 2 n_S³ ≤ d³  (Xe 닫힘이 d³ 안에). -/
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
