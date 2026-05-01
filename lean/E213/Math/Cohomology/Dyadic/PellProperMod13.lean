import E213.Math.Cohomology.Dyadic.PellProper

/-!
# Pell proper mod 13 — period 28 (INERT)

13 mod 8 = 5 (= -3), NQR ⇒ INERT.  Predict: 2(p+1) = 28.  TIGHT.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

set_option maxRecDepth 1024 in
theorem pellProper13_run_period_28 :
    ∀ k, (pellProperFSMmod 13 (by decide)).run (k + 28)
        = (pellProperFSMmod 13 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 13 (by decide)).step _
        = (pellProperFSMmod 13 (by decide)).step _
    rw [ih]

theorem pellProper13_bits_period_28 :
    ∀ k, (pellProperFSMmod 13 (by decide)).bits (k + 28)
        = (pellProperFSMmod 13 (by decide)).bits k := by
  intro k
  show (pellProperFSMmod 13 (by decide)).out
        ((pellProperFSMmod 13 (by decide)).run (k + 28))
       = (pellProperFSMmod 13 (by decide)).out
        ((pellProperFSMmod 13 (by decide)).run k)
  rw [pellProper13_run_period_28]

end E213.Math.Cohomology.Dyadic.Conjecture
