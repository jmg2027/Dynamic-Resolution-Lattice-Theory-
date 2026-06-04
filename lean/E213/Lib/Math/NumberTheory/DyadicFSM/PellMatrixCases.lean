import E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixAction
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModLarge
/-!
# Per-prime Pisano period closures via bridge — G119 Phase 3 closure

For each empirically-verified prime in the 23-prime Predictor chain,
derive the pellFSMmod bit-period claim via the bridge theorem:

  `pellCoeff p hp N = (0, 1)` ⟹ `pellFSMmod p hp` has bit-period N.

The hypothesis is `decide`-able per prime (matrix order computation
in finite GL_2(𝔽_p)).  The bridge then gives the FSM-period claim
without going through the FSM step-by-step.

This module **demonstrates** the bridge framework on the 23-prime
empirical evidence.  The universal-over-primes claim still requires
Phase 2 (FLT in 𝔽_p^*) + Phase 3.2/3.3 (legendre dispatch via
algebraic number theory).

For each prime p in the verified set:
  legendre (5, p) determines `predict := pisano_predict p hp`:
    legendre = 0 (ramified):  predict = 2p   — p=5 only
    legendre = 1 (split, QR): predict = (p-1)/2
    legendre = 2 (inert, NQR): predict = p+1

  By the bridge: `pellFSMmod p hp` has bit-period `predict`.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixCases

set_option maxRecDepth 2000

open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (pellFSMmod)
open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixAction
  (pellCoeff_period_implies_pellFSMmod_bits_period
   pellCoeff_period_implies_pellFSMmod_period)

/-! ## Ramified case (legendre = 0): p = 5 -/

theorem pell5_period_via_bridge :
    ∀ k, (pellFSMmod 5 (by decide)).bits (k + 10)
          = (pellFSMmod 5 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 5 (by decide) 10 (by rfl)

/-! ## Inert case (legendre = 2): predict = p+1
    Primes: 3, 7, 13, 17, 23, 37, 43, 47, 53, 67, 73 -/

theorem pell3_period_via_bridge :
    ∀ k, (pellFSMmod 3 (by decide)).bits (k + 4)
          = (pellFSMmod 3 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 3 (by decide) 4 (by rfl)

theorem pell7_period_via_bridge :
    ∀ k, (pellFSMmod 7 (by decide)).bits (k + 8)
          = (pellFSMmod 7 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 7 (by decide) 8 (by rfl)

theorem pell13_period_via_bridge :
    ∀ k, (pellFSMmod 13 (by decide)).bits (k + 14)
          = (pellFSMmod 13 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 13 (by decide) 14 (by rfl)

theorem pell17_period_via_bridge :
    ∀ k, (pellFSMmod 17 (by decide)).bits (k + 18)
          = (pellFSMmod 17 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 17 (by decide) 18 (by rfl)

theorem pell23_period_via_bridge :
    ∀ k, (pellFSMmod 23 (by decide)).bits (k + 24)
          = (pellFSMmod 23 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 23 (by decide) 24 (by rfl)

theorem pell37_period_via_bridge :
    ∀ k, (pellFSMmod 37 (by decide)).bits (k + 38)
          = (pellFSMmod 37 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 37 (by decide) 38 (by rfl)

theorem pell43_period_via_bridge :
    ∀ k, (pellFSMmod 43 (by decide)).bits (k + 44)
          = (pellFSMmod 43 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 43 (by decide) 44 (by rfl)

theorem pell47_period_via_bridge :
    ∀ k, (pellFSMmod 47 (by decide)).bits (k + 48)
          = (pellFSMmod 47 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 47 (by decide) 48 (by rfl)

theorem pell53_period_via_bridge :
    ∀ k, (pellFSMmod 53 (by decide)).bits (k + 54)
          = (pellFSMmod 53 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 53 (by decide) 54 (by rfl)

theorem pell67_period_via_bridge :
    ∀ k, (pellFSMmod 67 (by decide)).bits (k + 68)
          = (pellFSMmod 67 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 67 (by decide) 68 (by rfl)

theorem pell73_period_via_bridge :
    ∀ k, (pellFSMmod 73 (by decide)).bits (k + 74)
          = (pellFSMmod 73 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 73 (by decide) 74 (by rfl)

/-! ## Split case (legendre = 1): predict = (p-1)/2
    Primes: 11, 19, 29, 31, 41, 59, 61, 71, 79, 89, 101 -/

theorem pell11_period_via_bridge :
    ∀ k, (pellFSMmod 11 (by decide)).bits (k + 5)
          = (pellFSMmod 11 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 11 (by decide) 5 (by rfl)

theorem pell19_period_via_bridge :
    ∀ k, (pellFSMmod 19 (by decide)).bits (k + 9)
          = (pellFSMmod 19 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 19 (by decide) 9 (by rfl)

theorem pell29_period_via_bridge :
    ∀ k, (pellFSMmod 29 (by decide)).bits (k + 14)
          = (pellFSMmod 29 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 29 (by decide) 14 (by rfl)

theorem pell31_period_via_bridge :
    ∀ k, (pellFSMmod 31 (by decide)).bits (k + 15)
          = (pellFSMmod 31 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 31 (by decide) 15 (by rfl)

theorem pell41_period_via_bridge :
    ∀ k, (pellFSMmod 41 (by decide)).bits (k + 20)
          = (pellFSMmod 41 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 41 (by decide) 20 (by rfl)

theorem pell59_period_via_bridge :
    ∀ k, (pellFSMmod 59 (by decide)).bits (k + 29)
          = (pellFSMmod 59 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 59 (by decide) 29 (by rfl)

theorem pell61_period_via_bridge :
    ∀ k, (pellFSMmod 61 (by decide)).bits (k + 30)
          = (pellFSMmod 61 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 61 (by decide) 30 (by rfl)

theorem pell71_period_via_bridge :
    ∀ k, (pellFSMmod 71 (by decide)).bits (k + 35)
          = (pellFSMmod 71 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 71 (by decide) 35 (by rfl)

theorem pell79_period_via_bridge :
    ∀ k, (pellFSMmod 79 (by decide)).bits (k + 39)
          = (pellFSMmod 79 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 79 (by decide) 39 (by rfl)

theorem pell89_period_via_bridge :
    ∀ k, (pellFSMmod 89 (by decide)).bits (k + 44)
          = (pellFSMmod 89 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 89 (by decide) 44 (by rfl)

theorem pell101_period_via_bridge :
    ∀ k, (pellFSMmod 101 (by decide)).bits (k + 50)
          = (pellFSMmod 101 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 101 (by decide) 50 (by rfl)

end E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrixCases
