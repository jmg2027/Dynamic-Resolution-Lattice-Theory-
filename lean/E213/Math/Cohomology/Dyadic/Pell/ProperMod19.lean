import E213.Math.Cohomology.Dyadic.Pell.Proper

/-!
# Pell proper mod 19 — period 40 (INERT)

19 mod 8 = 3, NQR ⇒ INERT.  Predict: 2(p+1) = 40.  TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.Pell.ProperMod19

set_option maxRecDepth 2048 in
theorem pellProper19_run_period_40 :
    ∀ k, (pellProperFSMmod 19 (by decide)).run (k + 40)
        = (pellProperFSMmod 19 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 19 (by decide)).step _
        = (pellProperFSMmod 19 (by decide)).step _
    rw [ih]

theorem pellProper19_bits_period_40 :
    ∀ k, (pellProperFSMmod 19 (by decide)).bits (k + 40)
        = (pellProperFSMmod 19 (by decide)).bits k := by
  intro k
  show (pellProperFSMmod 19 (by decide)).out
        ((pellProperFSMmod 19 (by decide)).run (k + 40))
       = (pellProperFSMmod 19 (by decide)).out
        ((pellProperFSMmod 19 (by decide)).run k)
  rw [pellProper19_run_period_40]

end E213.Math.Cohomology.Dyadic.Pell.ProperMod19
