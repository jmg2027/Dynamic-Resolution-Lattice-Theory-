import E213.Math.Real213.FluxMVT

/-!
# Research.Real213FluxPolynomial

Phase AW: explicit local divergence forms for polynomial functions.
Each polynomial's flux at a bracket has a structural rfl form
giving direct computational access.

  localDivergence_square    : x ↦ x² flux at db
  localDivergence_cube      : x ↦ x³ flux at db
  localDivergence_pow_form  : x ↦ cutPow x n flux at db (generic)
-/

namespace E213.Math.Real213.FluxPolynomial

open E213.Firmware E213.Hypervisor

namespace FluxCut

/-- Local divergence of x² has explicit form: scaled (right² - left²)
    structurally, before any simplification. -/
theorem localDivergence_square (db : DyadicBracket) :
    localDivergence (fun x => cutMul x x) db
      = { forward := cutScale (2^db.expE) 1 (cutMul db.rightCut db.rightCut),
          backward := cutScale (2^db.expE) 1 (cutMul db.leftCut db.leftCut) } :=
  rfl

/-- Local divergence of x³ has explicit form. -/
theorem localDivergence_cube (db : DyadicBracket) :
    localDivergence (fun x => cutMul x (cutMul x x)) db
      = { forward := cutScale (2^db.expE) 1
            (cutMul db.rightCut (cutMul db.rightCut db.rightCut)),
          backward := cutScale (2^db.expE) 1
            (cutMul db.leftCut (cutMul db.leftCut db.leftCut)) } :=
  rfl

/-- Generic cutPow flux: at any n. -/
theorem localDivergence_pow_form (n : Nat) (db : DyadicBracket) :
    localDivergence (fun x => cutPow x n) db
      = { forward := cutScale (2^db.expE) 1 (cutPow db.rightCut n),
          backward := cutScale (2^db.expE) 1 (cutPow db.leftCut n) } :=
  rfl

/-- Quartic divergence: explicit form. -/
theorem localDivergence_quartic (db : DyadicBracket) :
    localDivergence (fun x => cutMul (cutMul x x) (cutMul x x)) db
      = { forward := cutScale (2^db.expE) 1
            (cutMul (cutMul db.rightCut db.rightCut)
                    (cutMul db.rightCut db.rightCut)),
          backward := cutScale (2^db.expE) 1
            (cutMul (cutMul db.leftCut db.leftCut)
                    (cutMul db.leftCut db.leftCut)) } :=
  rfl

/-- Phase AW capstone: polynomial divergence forms (rfl-clean). -/
theorem polynomial_flux_capstone (n : Nat) (db : DyadicBracket) :
    (localDivergence (fun x => cutMul x x) db).forward
      = cutScale (2^db.expE) 1 (cutMul db.rightCut db.rightCut)
    ∧ (localDivergence (fun x => cutPow x n) db).forward
      = cutScale (2^db.expE) 1 (cutPow db.rightCut n)
    ∧ (localDivergence (fun x => cutPow x n) db).backward
      = cutScale (2^db.expE) 1 (cutPow db.leftCut n) := ⟨rfl, rfl, rfl⟩

end FluxCut

end E213.Math.Real213.FluxPolynomial
