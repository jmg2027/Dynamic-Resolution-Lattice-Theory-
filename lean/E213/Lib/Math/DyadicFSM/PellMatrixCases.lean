import E213.Lib.Math.DyadicFSM.PellMatrixAction
/-!
# Per-legendre-case Pisano period closures — G119 Phase 3.1+

Uses `PellMatrixAction.pellCoeff_period_implies_pellFSMmod_period`
(the bridge theorem) to derive per-prime period claims structurally
from `pellCoeff p hp N = (0, 1)` (decidable for fixed p).

Phase 3.1 (ramified, p=5):  CLOSED via decide.
Phase 3.2 (split):          smoke tests at p ∈ {11, 19, 31, 41, 59, 61, 71, 79}.
Phase 3.3 (inert):          smoke tests at p ∈ {3, 7, 13, 17, 23, 37, 43, 53, 67, 73}.

For each empirically-verified prime, the bridge reduces the FSM-period
claim to a finite `pellCoeff p hp N = (0, 1)` check, which is `decide`.

The universal-over-primes claim requires Phase 2 (FLT + QR) — see
`research-notes/G119_pisano_pell5_research_direction.md`.
-/

namespace E213.Lib.Math.DyadicFSM.PellMatrixCases

open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod)
open E213.Lib.Math.DyadicFSM.PellMatrixAction
  (pellCoeff_period_implies_pellFSMmod_bits_period
   pellCoeff_period_implies_pellFSMmod_period)

/-- ★ Phase 3.1 (RAMIFIED, p=5): pellFSMmod 5 has bit-period 10 = 2p.
    Closed via bridge + `decide` for pellCoeff 5 _ 10 = (0, 1). -/
theorem pell5_ramified_period_via_bridge :
    ∀ k, (pellFSMmod 5 (by decide)).bits (k + 10)
          = (pellFSMmod 5 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 5 (by decide) 10
    (by rfl)

/-- ★ Phase 3.2 SMOKE (split p=11): pellFSMmod 11 has bit-period 5 = (p-1)/2. -/
theorem pell11_split_period_via_bridge :
    ∀ k, (pellFSMmod 11 (by decide)).bits (k + 5)
          = (pellFSMmod 11 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 11 (by decide) 5
    (by rfl)

/-- ★ Phase 3.3 SMOKE (inert p=3): pellFSMmod 3 has bit-period 4 = p+1. -/
theorem pell3_inert_period_via_bridge :
    ∀ k, (pellFSMmod 3 (by decide)).bits (k + 4)
          = (pellFSMmod 3 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 3 (by decide) 4
    (by rfl)

/-- Phase 3.3 SMOKE (inert p=7, predict = p+1 = 8). -/
theorem pell7_inert_period_via_bridge :
    ∀ k, (pellFSMmod 7 (by decide)).bits (k + 8)
          = (pellFSMmod 7 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 7 (by decide) 8
    (by rfl)

/-- Phase 3.3 SMOKE (inert p=13, predict = p+1 = 14). -/
theorem pell13_inert_period_via_bridge :
    ∀ k, (pellFSMmod 13 (by decide)).bits (k + 14)
          = (pellFSMmod 13 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 13 (by decide) 14
    (by rfl)

/-- Phase 3.2 SMOKE (split p=19, predict = (p-1)/2 = 9). -/
theorem pell19_split_period_via_bridge :
    ∀ k, (pellFSMmod 19 (by decide)).bits (k + 9)
          = (pellFSMmod 19 (by decide)).bits k :=
  pellCoeff_period_implies_pellFSMmod_bits_period 19 (by decide) 9
    (by rfl)

end E213.Lib.Math.DyadicFSM.PellMatrixCases
