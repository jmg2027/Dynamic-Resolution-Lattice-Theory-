import E213.Lib.Math.DyadicFSM.Pell.ProperSmall
import E213.Lib.Math.DyadicFSM.Pell.ProperMod

import E213.Lib.Math.DyadicFSM.Pell.Proper
/-!
# Pell-proper (Δ=8) — 8-prime evidence capstone

  | p  | (8/p) | Branch | π(p) | predict (Pisano)  | match |
  |  3 |  -1   | inert  |   8  | 2(p+1) =  8       | TIGHT |
  |  5 |  -1   | inert  |  12  | 2(p+1) = 12       | TIGHT |
  |  7 |   1   | split  |   6  | p-1    =  6       | TIGHT |
  | 11 |  -1   | inert  |  24  | 2(p+1) = 24       | TIGHT | NEW
  | 13 |  -1   | inert  |  28  | 2(p+1) = 28       | TIGHT | NEW
  | 17 |   1   | split  |  16  | p-1    = 16       | TIGHT | NEW
  | 19 |  -1   | inert  |  40  | 2(p+1) = 40       | TIGHT | NEW
  | 23 |   1   | split  |  22  | p-1    = 22       | TIGHT | NEW

All 8 primes TIGHT.  Coverage:
  Inert (5): {3, 5, 11, 13, 19} — 2(p+1) formula
  Split (3): {7, 17, 23}        — p-1 formula

Pell-proper (eigenvalues 1±√2, units of ℤ[√2]) parallels the
established Pell (Δ=5) and Fibonacci (Δ=5) frameworks.  Same
Galois lens (Legendre via D=8 = 2³ ≡ 2 mod p), different period
formula (no /2 in split, no factor of 2 in ramified).

Three Pisano framework families now established at 8-prime baseline:
  - Pell (Δ=5):       17 primes (commit 3ad63d8)
  - Pell-proper (Δ=8): 8 primes (this commit)
  - Fibonacci (Δ=5):   8 primes (commit 355dc4d)
-/

namespace E213.Lib.Math.DyadicFSM.Pell.Proper8

open E213.Lib.Math.DyadicFSM.Pell.Proper (pellProperFSMmod)
open E213.Lib.Math.DyadicFSM.Pell.ProperSmall (pellProper3_run_period_8 pellProper5_run_period_12 pellProper7_run_period_6)
open E213.Lib.Math.DyadicFSM.Pell.ProperMod11 (pellProper11_bits_period_24)
open E213.Lib.Math.DyadicFSM.Pell.ProperMod13 (pellProper13_bits_period_28)
open E213.Lib.Math.DyadicFSM.Pell.ProperMod17 (pellProper17_bits_period_16)
open E213.Lib.Math.DyadicFSM.Pell.ProperMod19 (pellProper19_bits_period_40)
open E213.Lib.Math.DyadicFSM.Pell.ProperMod23 (pellProper23_bits_period_22)

/-- ★★★★★★★★ Pell-proper 8-prime capstone (all bit periods). -/
theorem pellProper_8prime_capstone :
    (∀ k, (pellProperFSMmod 3 (by decide)).run (k + 8)
        = (pellProperFSMmod 3 (by decide)).run k)
    ∧ (∀ k, (pellProperFSMmod 5 (by decide)).run (k + 12)
        = (pellProperFSMmod 5 (by decide)).run k)
    ∧ (∀ k, (pellProperFSMmod 7 (by decide)).run (k + 6)
        = (pellProperFSMmod 7 (by decide)).run k)
    ∧ (∀ k, (pellProperFSMmod 11 (by decide)).bits (k + 24)
        = (pellProperFSMmod 11 (by decide)).bits k)
    ∧ (∀ k, (pellProperFSMmod 13 (by decide)).bits (k + 28)
        = (pellProperFSMmod 13 (by decide)).bits k)
    ∧ (∀ k, (pellProperFSMmod 17 (by decide)).bits (k + 16)
        = (pellProperFSMmod 17 (by decide)).bits k)
    ∧ (∀ k, (pellProperFSMmod 19 (by decide)).bits (k + 40)
        = (pellProperFSMmod 19 (by decide)).bits k)
    ∧ (∀ k, (pellProperFSMmod 23 (by decide)).bits (k + 22)
        = (pellProperFSMmod 23 (by decide)).bits k) :=
  ⟨pellProper3_run_period_8,
   pellProper5_run_period_12,
   pellProper7_run_period_6,
   pellProper11_bits_period_24,
   pellProper13_bits_period_28,
   pellProper17_bits_period_16,
   pellProper19_bits_period_40,
   pellProper23_bits_period_22⟩

end E213.Lib.Math.DyadicFSM.Pell.Proper8
