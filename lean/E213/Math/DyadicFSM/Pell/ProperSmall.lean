import E213.Math.DyadicFSM.Pell.Proper

/-!
# Pell proper concrete instances — mod {3, 5, 7}

Verifies the Legendre-Pisano framework for Pell proper:

  | p | (8/p)  | Branch | TIGHT period | Formula     |
  | 3 | 2 (NQR)| inert  |     8        | 2(p+1) = 8  |
  | 5 | 2 (NQR)| inert  |    12        | 2(p+1) = 12 |
  | 7 | 1 (QR) | split  |     6        | p-1    = 6  |

All three TIGHT periods exactly match the Legendre-predicted values.
-/

namespace E213.Math.DyadicFSM.Pell.ProperSmall

open E213.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)

/-- ★★★ Pell proper mod 3: period 8 = 2(p+1) (inert). -/
theorem pellProper3_run_period_8 :
    ∀ k, (pellProperFSMmod 3 (by decide)).run (k + 8)
        = (pellProperFSMmod 3 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 3 (by decide)).step _
        = (pellProperFSMmod 3 (by decide)).step _
    rw [ih]

/-- ★★★ Pell proper mod 5: period 12 = 2(p+1) (inert). -/
theorem pellProper5_run_period_12 :
    ∀ k, (pellProperFSMmod 5 (by decide)).run (k + 12)
        = (pellProperFSMmod 5 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 5 (by decide)).step _
        = (pellProperFSMmod 5 (by decide)).step _
    rw [ih]

/-- ★★★ Pell proper mod 7: period 6 = p-1 (split). -/
theorem pellProper7_run_period_6 :
    ∀ k, (pellProperFSMmod 7 (by decide)).run (k + 6)
        = (pellProperFSMmod 7 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 7 (by decide)).step _
        = (pellProperFSMmod 7 (by decide)).step _
    rw [ih]

end E213.Math.DyadicFSM.Pell.ProperSmall
