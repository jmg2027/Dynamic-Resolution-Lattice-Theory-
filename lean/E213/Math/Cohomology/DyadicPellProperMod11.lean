import E213.Math.Cohomology.DyadicPellProper

/-!
# Pell proper mod 11 — period 24 (INERT)

11 mod 8 = 3, NQR ⇒ INERT.  Pell-proper predict: 2(p+1) = 24.  TIGHT.
-/

namespace E213.Math.Cohomology.DyadicConjecture

set_option maxRecDepth 1024 in
theorem pellProper11_run_period_24 :
    ∀ k, (pellProperFSMmod 11 (by decide)).run (k + 24)
        = (pellProperFSMmod 11 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 11 (by decide)).step _
        = (pellProperFSMmod 11 (by decide)).step _
    rw [ih]

theorem pellProper11_bits_period_24 :
    ∀ k, (pellProperFSMmod 11 (by decide)).bits (k + 24)
        = (pellProperFSMmod 11 (by decide)).bits k := by
  intro k
  show (pellProperFSMmod 11 (by decide)).out
        ((pellProperFSMmod 11 (by decide)).run (k + 24))
       = (pellProperFSMmod 11 (by decide)).out
        ((pellProperFSMmod 11 (by decide)).run k)
  rw [pellProper11_run_period_24]

end E213.Math.Cohomology.DyadicConjecture
