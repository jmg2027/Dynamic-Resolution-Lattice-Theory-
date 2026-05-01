import E213.Math.Cohomology.DyadicPellProper

/-!
# Pell proper mod 17 — period 16 (SPLIT, first instance)

17 mod 8 = 1, QR ⇒ SPLIT.  Predict: p-1 = 16.  TIGHT.

First SPLIT instance for Pell-proper.
-/

namespace E213.Math.Cohomology.DyadicConjecture

theorem pellProper17_run_period_16 :
    ∀ k, (pellProperFSMmod 17 (by omega)).run (k + 16)
        = (pellProperFSMmod 17 (by omega)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 17 (by omega)).step _
        = (pellProperFSMmod 17 (by omega)).step _
    rw [ih]

theorem pellProper17_bits_period_16 :
    ∀ k, (pellProperFSMmod 17 (by omega)).bits (k + 16)
        = (pellProperFSMmod 17 (by omega)).bits k := by
  intro k
  show (pellProperFSMmod 17 (by omega)).out
        ((pellProperFSMmod 17 (by omega)).run (k + 16))
       = (pellProperFSMmod 17 (by omega)).out
        ((pellProperFSMmod 17 (by omega)).run k)
  rw [pellProper17_run_period_16]

end E213.Math.Cohomology.DyadicConjecture
