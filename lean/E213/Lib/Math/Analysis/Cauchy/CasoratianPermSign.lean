import E213.Lib.Math.Analysis.Cauchy.CasoratianDeterminant
import E213.Lib.Math.Algebra.Linalg213.CyclicShiftSign
import E213.Lib.Math.Algebra.Linalg213.PermMatrixDet

/-!
# Cauchy.CasoratianPermSign — the Casoratian multiplier sign IS a permutation sign

The all-orders Casoratian law multiplies the Hankel determinant each step by
`altSign(k−1)·a 0` (`CasoratianDeterminant.casoratian_det_step`); the sign comes from the
companion (cyclic-shift) determinant `det_companion : det(companion a (m+1)) = altSign m · a 0`.

This file shows the companion/Casoratian multiplier sign IS a permutation sign: that
sign `altSign m` is exactly the **permutation sign** `psign` of the underlying `(m+1)`-cycle
`(0 1 … m)` (`CyclicShiftSign.cycShift_psign`).  So the companion determinant joins the
"permutation under three readouts" (`det(permMatrix)` = `psign` = Legendre/Zolotarev,
`theory/essays/synthesis/the_permutation_under_three_readouts.md`) as a **fourth** instance of
the single inversion-sign readout — the Casoratian depth multiplier carries the sign of the
shift cycle.

All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.CasoratianPermSign

open E213.Lib.Math.Algebra.Linalg213.DetN (det altSign)
open E213.Lib.Math.Analysis.Cauchy.CasoratianDeterminant (companion det_companion)
open E213.Lib.Math.Algebra.Linalg213.Permutation (psign LPerm iota)
open E213.Lib.Math.Algebra.Linalg213.CyclicShiftSign (cycShift cycShift_psign cycShift_perm_iota)
open E213.Lib.Math.Algebra.Linalg213.PermMatrixDet (permMatrix det_permMatrix)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (permsOf_complete)

/-- ★★★★ **The companion determinant is a permutation sign times `a 0`.**
    `det(companion a (m+1)) = psign(cycShift m) · a 0` — the order-`(m+1)` Casoratian
    multiplier's sign is the sign of the cyclic-shift permutation `(0 1 … m)`, not just
    `altSign m`.  Combines `det_companion` (sign = `altSign m`) with `cycShift_psign`
    (`psign(cycShift m) = altSign m`). -/
theorem companion_det_is_perm_sign (a : Nat → Int) (m : Nat) :
    det (m + 1) (companion a (m + 1)) = psign (cycShift m) * a 0 := by
  rw [det_companion a m, cycShift_psign m]

/-- ★★★★★ **The fourth readout.**  The companion/Casoratian sign is the permutation sign of a
    genuine permutation: `cycShift m` is a rearrangement of `[0,…,m]` (`cycShift_perm_iota`),
    and the companion determinant carries its `psign`.  This places the depth multiplier on the
    same inversion-sign readout as `det(permMatrix)` / Legendre / Zolotarev. -/
theorem casoratian_sign_is_cycle_psign (a : Nat → Int) (m : Nat) :
    LPerm (cycShift m) (iota (m + 1))
    ∧ det (m + 1) (companion a (m + 1)) = psign (cycShift m) * a 0 :=
  ⟨cycShift_perm_iota m, companion_det_is_perm_sign a m⟩

/-! ## The middle readout, made literal -/

/-- ★★★ **The shift cycle's permutation-matrix determinant is `altSign m`.**  Routing
    `cycShift m` (a certified permutation of `[0,…,m]`) through `det_permMatrix`
    (`det(permMatrix σ) = psign σ`) gives `det(permMatrix (cycShift m)) = altSign m` — the
    cyclic-shift orientation read as a determinant. -/
theorem det_permMatrix_cycShift (m : Nat) :
    det (m + 1) (permMatrix (cycShift m)) = altSign m := by
  rw [det_permMatrix (m + 1) (cycShift m)
        (permsOf_complete (iota (m + 1)) (cycShift m) (cycShift_perm_iota m)),
      cycShift_psign m]

/-- ★★★★★ **The companion determinant IS a permutation-matrix determinant.**
    `det(companion a (m+1)) = det(permMatrix (cycShift m)) · a 0`: the Casoratian depth
    multiplier's sign is *literally* the determinant of the cyclic-shift permutation matrix —
    the recurrence-determinant and the permutation-determinant readouts coincide on the shift
    cycle, completing the fourth instance of "permutation under three readouts". -/
theorem companion_det_eq_permMatrix_det (a : Nat → Int) (m : Nat) :
    det (m + 1) (companion a (m + 1)) = det (m + 1) (permMatrix (cycShift m)) * a 0 := by
  rw [det_companion a m, det_permMatrix_cycShift m]

end E213.Lib.Math.Analysis.Cauchy.CasoratianPermSign
