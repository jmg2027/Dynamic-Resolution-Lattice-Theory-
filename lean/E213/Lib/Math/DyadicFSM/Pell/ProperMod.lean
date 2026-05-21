import E213.Lib.Math.DyadicFSM.Pell.Proper

/-!
# Pell.ProperMod — Pell-equation per-prime instances (p ∈ {11,13,17,19,23})

5 instances of Pell-FSM proper-period evidence at primes
{11, 13, 17, 19, 23}.  Each = direct ArithFSM mod p check that
the Pell sequence's period equals the formula bound.

Per-p namespaces preserved (`Pell.ProperMod{p}`).
-/

namespace E213.Lib.Math.DyadicFSM.Pell.ProperMod11

open E213.Lib.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)

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

end E213.Lib.Math.DyadicFSM.Pell.ProperMod11

namespace E213.Lib.Math.DyadicFSM.Pell.ProperMod13

open E213.Lib.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)

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

end E213.Lib.Math.DyadicFSM.Pell.ProperMod13

namespace E213.Lib.Math.DyadicFSM.Pell.ProperMod17

open E213.Lib.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)

theorem pellProper17_run_period_16 :
    ∀ k, (pellProperFSMmod 17 (by decide)).run (k + 16)
        = (pellProperFSMmod 17 (by decide)).run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show (pellProperFSMmod 17 (by decide)).step _
        = (pellProperFSMmod 17 (by decide)).step _
    rw [ih]

theorem pellProper17_bits_period_16 :
    ∀ k, (pellProperFSMmod 17 (by decide)).bits (k + 16)
        = (pellProperFSMmod 17 (by decide)).bits k := by
  intro k
  show (pellProperFSMmod 17 (by decide)).out
        ((pellProperFSMmod 17 (by decide)).run (k + 16))
       = (pellProperFSMmod 17 (by decide)).out
        ((pellProperFSMmod 17 (by decide)).run k)
  rw [pellProper17_run_period_16]

end E213.Lib.Math.DyadicFSM.Pell.ProperMod17

namespace E213.Lib.Math.DyadicFSM.Pell.ProperMod19

open E213.Lib.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)

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

end E213.Lib.Math.DyadicFSM.Pell.ProperMod19

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
