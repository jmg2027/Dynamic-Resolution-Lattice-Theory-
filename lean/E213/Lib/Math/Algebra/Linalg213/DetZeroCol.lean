import E213.Lib.Math.Algebra.Linalg213.CayleyHamilton

/-!
# Linalg213 — a zero column ⟹ `det = 0`

The **column** analog of `det_zero_row`, proved directly from the Leibniz form (no transpose
needed): every permutation hits the zero column exactly once, so every Leibniz term carries a zero
factor.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.DetZeroCol

open E213.Lib.Math.Algebra.Linalg213.Permutation (sumZ iota perms prodDiagFrom leibTerm leibDet psign)
open E213.Lib.Math.Algebra.Linalg213.Permutation.LPerm (symm)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_eq_of_mem permsOf_sound)
open E213.Lib.Math.Algebra.Linalg213.PermClosure.LPerm (mem)
open E213.Lib.Math.Algebra.Linalg213.DetN (det)
open E213.Lib.Math.Algebra.Linalg213.Laplace (leibDet_eq_det mem_iota_of_lt)
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton (sumZ_map_zero mul_zero')

/-- A diagonal product with a zero-column value present is `0`. -/
theorem prodDiagFrom_zero_of_mem {c : Nat} {M : Nat → Nat → Int} (hz : ∀ i, M i c = 0) :
    ∀ (p : List Nat) (k : Nat), c ∈ p → prodDiagFrom M k p = 0
  | [],      _, hmem => nomatch hmem
  | q :: qs, k, hmem => by
    show M k q * prodDiagFrom M (k + 1) qs = 0
    cases hmem with
    | head      => rw [hz k, E213.Meta.Int213.zero_mul]
    | tail _ h  => rw [prodDiagFrom_zero_of_mem hz qs (k + 1) h, mul_zero']

/-- Every `c < n` occurs in every permutation of `[0,…,n−1]`. -/
theorem mem_perm_of_lt {n c : Nat} (hc : c < n) {p : List Nat} (hp : p ∈ perms n) : c ∈ p :=
  mem (symm (permsOf_sound (iota n) p hp)) (mem_iota_of_lt hc)

/-- ★★ **A zero column ⟹ `det = 0`** (the column analog of `det_zero_row`, via the Leibniz form). -/
theorem det_zero_col (n c : Nat) (hc : c < n) (M : Nat → Nat → Int) (hz : ∀ i, M i c = 0) :
    det n M = 0 := by
  rw [← leibDet_eq_det]
  show sumZ ((perms n).map (leibTerm M)) = 0
  rw [map_eq_of_mem (leibTerm M) (fun _ => 0)
        (fun p hp => by
          show psign p * prodDiagFrom M 0 p = 0
          rw [prodDiagFrom_zero_of_mem hz p 0 (mem_perm_of_lt hc hp), mul_zero']),
      sumZ_map_zero]

end E213.Lib.Math.Algebra.Linalg213.DetZeroCol
