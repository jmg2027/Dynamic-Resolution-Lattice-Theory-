import E213.Math.Cohomology.DyadicPellProper

/-!
# Pell proper mod 13 — period 28 (INERT)

13 mod 8 = 5 (= -3), NQR ⇒ INERT.  Predict: 2(p+1) = 28.  TIGHT.
-/

namespace E213.Math.Cohomology.DyadicConjecture

set_option maxRecDepth 1024 in
theorem pellProper13_run_period_28 :
    ∀ k, (pellProperFSMmod 13 (by omega)).run (k + 28)
        = (pellProperFSMmod 13 (by omega)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 13 (by omega)).step _
        = (pellProperFSMmod 13 (by omega)).step _
    rw [ih]

theorem pellProper13_bits_period_28 :
    ∀ k, (pellProperFSMmod 13 (by omega)).bits (k + 28)
        = (pellProperFSMmod 13 (by omega)).bits k := by
  intro k
  show (pellProperFSMmod 13 (by omega)).out
        ((pellProperFSMmod 13 (by omega)).run (k + 28))
       = (pellProperFSMmod 13 (by omega)).out
        ((pellProperFSMmod 13 (by omega)).run k)
  rw [pellProper13_run_period_28]

end E213.Math.Cohomology.DyadicConjecture
