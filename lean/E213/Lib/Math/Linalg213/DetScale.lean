import E213.Lib.Math.Linalg213.Laplace

/-!
# Linalg213 — the scaling determinant `det (c·M) = cⁿ · det M`

Scaling every entry of an `n×n` matrix by `c` scales the determinant by `cⁿ` — each of the `n`
rows of a Leibniz term contributes one factor `c`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.DetScale

open E213.Lib.Math.Linalg213.Permutation (sumZ perms prodDiagFrom leibTerm leibDet psign)
open E213.Lib.Math.Linalg213.PermClosure (perm_length sumZ_map_smul map_eq_of_mem)
open E213.Lib.Math.Linalg213.DetN (det)
open E213.Lib.Math.Linalg213.Laplace (leibDet_eq_det)
open E213.Meta.Int213.PolyIntM (powInt)

/-- Scaling the matrix scales the diagonal product by `c^{|p|}`. -/
theorem prodDiagFrom_smul (c : Int) (M : Nat → Nat → Int) : ∀ (i : Nat) (p : List Nat),
    prodDiagFrom (fun a b => c * M a b) i p = powInt c p.length * prodDiagFrom M i p
  | _, []      => by
    show (1 : Int) = powInt c 0 * 1
    rw [show powInt c 0 = 1 from rfl, Int.one_mul]
  | i, q :: qs => by
    show c * M i q * prodDiagFrom (fun a b => c * M a b) (i + 1) qs
       = powInt c (qs.length + 1) * (M i q * prodDiagFrom M (i + 1) qs)
    rw [prodDiagFrom_smul c M (i + 1) qs]
    show c * M i q * (powInt c qs.length * prodDiagFrom M (i + 1) qs)
       = powInt c qs.length * c * (M i q * prodDiagFrom M (i + 1) qs)
    ring_intZ

/-- Scaling the matrix scales each Leibniz term by `c^{|p|}`. -/
theorem leibTerm_smul (c : Int) (M : Nat → Nat → Int) (p : List Nat) :
    leibTerm (fun a b => c * M a b) p = powInt c p.length * leibTerm M p := by
  show psign p * prodDiagFrom (fun a b => c * M a b) 0 p
     = powInt c p.length * (psign p * prodDiagFrom M 0 p)
  rw [prodDiagFrom_smul c M 0 p]
  ring_intZ

/-- ★ **The Leibniz determinant scales by `cⁿ`**: `leibDet n (c·M) = cⁿ · leibDet n M`. -/
theorem leibDet_smul (n : Nat) (c : Int) (M : Nat → Nat → Int) :
    leibDet n (fun a b => c * M a b) = powInt c n * leibDet n M := by
  show sumZ ((perms n).map (leibTerm (fun a b => c * M a b)))
     = powInt c n * sumZ ((perms n).map (leibTerm M))
  rw [map_eq_of_mem (leibTerm (fun a b => c * M a b)) (fun p => powInt c n * leibTerm M p)
        (fun p hp => by
          show leibTerm (fun a b => c * M a b) p = powInt c n * leibTerm M p
          rw [leibTerm_smul c M p, perm_length hp]),
      sumZ_map_smul]

/-- ★★ **The scaling determinant**: `det n (c·M) = cⁿ · det n M`. -/
theorem det_smul (n : Nat) (c : Int) (M : Nat → Nat → Int) :
    det n (fun a b => c * M a b) = powInt c n * det n M := by
  rw [← leibDet_eq_det n (fun a b => c * M a b), leibDet_smul n c M, leibDet_eq_det n M]

end E213.Lib.Math.Linalg213.DetScale
