import E213.Math.Cohomology.DyadicPellProper

/-!
# Pell proper mod 19 — period 40 (INERT)

19 mod 8 = 3, NQR ⇒ INERT.  Predict: 2(p+1) = 40.  TIGHT.
-/

namespace E213.Math.Cohomology.DyadicConjecture

set_option maxRecDepth 2048 in
theorem pellProper19_run_period_40 :
    ∀ k, (pellProperFSMmod 19 (by omega)).run (k + 40)
        = (pellProperFSMmod 19 (by omega)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 19 (by omega)).step _
        = (pellProperFSMmod 19 (by omega)).step _
    rw [ih]

theorem pellProper19_bits_period_40 :
    ∀ k, (pellProperFSMmod 19 (by omega)).bits (k + 40)
        = (pellProperFSMmod 19 (by omega)).bits k := by
  intro k
  show (pellProperFSMmod 19 (by omega)).out
        ((pellProperFSMmod 19 (by omega)).run (k + 40))
       = (pellProperFSMmod 19 (by omega)).out
        ((pellProperFSMmod 19 (by omega)).run k)
  rw [pellProper19_run_period_40]

end E213.Math.Cohomology.DyadicConjecture
