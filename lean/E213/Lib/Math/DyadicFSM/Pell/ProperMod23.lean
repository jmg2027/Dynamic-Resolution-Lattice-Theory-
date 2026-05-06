import E213.Lib.Math.DyadicFSM.Pell.Proper

/-!
# Pell proper mod 23 — period 22 (SPLIT, second instance)

23 mod 8 = 7 (= -1), QR ⇒ SPLIT.  Predict: p-1 = 22.  TIGHT.
-/

namespace E213.Lib.Math.DyadicFSM.Pell.ProperMod23

open E213.Lib.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)

set_option maxRecDepth 1024 in
theorem pellProper23_run_period_22 :
    ∀ k, (pellProperFSMmod 23 (by decide)).run (k + 22)
        = (pellProperFSMmod 23 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 23 (by decide)).step _
        = (pellProperFSMmod 23 (by decide)).step _
    rw [ih]

theorem pellProper23_bits_period_22 :
    ∀ k, (pellProperFSMmod 23 (by decide)).bits (k + 22)
        = (pellProperFSMmod 23 (by decide)).bits k := by
  intro k
  show (pellProperFSMmod 23 (by decide)).out
        ((pellProperFSMmod 23 (by decide)).run (k + 22))
       = (pellProperFSMmod 23 (by decide)).out
        ((pellProperFSMmod 23 (by decide)).run k)
  rw [pellProper23_run_period_22]

end E213.Lib.Math.DyadicFSM.Pell.ProperMod23
