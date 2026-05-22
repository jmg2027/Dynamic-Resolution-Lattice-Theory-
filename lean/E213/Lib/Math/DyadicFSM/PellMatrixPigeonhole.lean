import E213.Lib.Math.DyadicFSM.PellMatrixInverse
import E213.Lib.Math.DyadicFSM.PellMatrixAction
import E213.Lib.Math.DyadicFSM.ArithFSM.InvertibleArithFSM2
/-!
# Existential Pisano period via the generic invertible-FSM template — G119 Phase 2

`pellCoeffFSM p hp` (the Cayley-Hamilton coefficient FSM for the Pell
matrix `M = [[2, 1], [1, 1]]`) is an `InvertibleArithFSM2 p` —
`stepInv` is the matrix-inverse action and `inv_left` is
`PellMatrixInverse.stepInv_step`.

Wrapping `pellCoeffFSM` in the `InvertibleArithFSM2` structure makes
the generic `exists_period` theorem applicable; the Pisano-period
existential is then a 1-line corollary.  Bridging via
`pellCoeff_period_implies_pellFSMmod_period` (and the bits variant)
lifts the existential up to the user-facing FSM run/bits sequences.

All declarations PURE.

The G119 Phase 3 work (predictive form `N = pisano_predict p` via
FLT + legendre dispatch) remains a multi-session research direction
documented in `research-notes/G119_pisano_pell5_research_direction.md`.
-/

namespace E213.Lib.Math.DyadicFSM.PellMatrixPigeonhole

open E213.Lib.Math.DyadicFSM.PellMatrix
  (pellCoeff pellCoeffFSM pellCoeffFSM_run_eq_pellCoeff stepInv)
open E213.Lib.Math.DyadicFSM.PellMatrixInverse (stepInv_step)
open E213.Lib.Math.DyadicFSM.PellMatrixAction
  (pellCoeff_period_implies_pellFSMmod_period
   pellCoeff_period_implies_pellFSMmod_bits_period)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod InvertibleArithFSM2)

/-- Lift `pellCoeffFSM p hp` to an `InvertibleArithFSM2 p` by
    pairing it with the Cayley-Hamilton step inverse + the
    universal left-cancellation `stepInv_step`. -/
def pellCoeffInvertibleFSM (p : Nat) (hp : 1 < p) : InvertibleArithFSM2 p where
  toArithFSM2 := pellCoeffFSM p hp
  stepInv     := stepInv p hp
  inv_left    := stepInv_step p hp

/-- ★ **Existential Pisano period** for the Pell C-H coefficients.
    1-line corollary of `InvertibleArithFSM2.exists_period` applied
    to `pellCoeffInvertibleFSM`, then unfolding
    `(pellCoeffFSM p hp).run k = pellCoeff p hp k`.  PURE. -/
theorem exists_pisano_period (p : Nat) (hp : 1 < p) :
    ∃ N, 0 < N ∧ N ≤ p * p ∧ pellCoeff p hp N = pellCoeff p hp 0 := by
  obtain ⟨N, hN_pos, hN_le, hN_run⟩ :=
    InvertibleArithFSM2.exists_period (pellCoeffInvertibleFSM p hp) hp
  -- `(pellCoeffInvertibleFSM p hp).run = (pellCoeffFSM p hp).run` by defeq
  -- (the `extends` projection resolves to `pellCoeffFSM` via the
  -- `toArithFSM2 := pellCoeffFSM p hp` field).
  have hN_fsm : (pellCoeffFSM p hp).run N = (pellCoeffFSM p hp).run 0 := hN_run
  rw [pellCoeffFSM_run_eq_pellCoeff,
      pellCoeffFSM_run_eq_pellCoeff] at hN_fsm
  exact ⟨N, hN_pos, hN_le, hN_fsm⟩

/-- ★ **Existential FSM-period** at the (1, 1) orbit (run version):
    `pellFSMmod p hp` is periodic in `≤ p²` steps.  Bridge corollary
    of `exists_pisano_period` + `pellCoeff_period_implies_pellFSMmod_period`.
    PURE. -/
theorem exists_pellFSMmod_period (p : Nat) (hp : 1 < p) :
    ∃ N, 0 < N ∧ N ≤ p * p
      ∧ ∀ k, (pellFSMmod p hp).run (k + N) = (pellFSMmod p hp).run k := by
  obtain ⟨N, hN_pos, hN_le, hN_eq⟩ := exists_pisano_period p hp
  exact ⟨N, hN_pos, hN_le,
    pellCoeff_period_implies_pellFSMmod_period p hp N hN_eq⟩

/-- ★ **Existential FSM-period** (bits version): the
    `(pellFSMmod p hp).bits` sequence is periodic in `≤ p²` steps.
    Bridge corollary via `pellCoeff_period_implies_pellFSMmod_bits_period`.
    PURE. -/
theorem exists_pellFSMmod_bits_period (p : Nat) (hp : 1 < p) :
    ∃ N, 0 < N ∧ N ≤ p * p
      ∧ ∀ k, (pellFSMmod p hp).bits (k + N) = (pellFSMmod p hp).bits k := by
  obtain ⟨N, hN_pos, hN_le, hN_eq⟩ := exists_pisano_period p hp
  exact ⟨N, hN_pos, hN_le,
    pellCoeff_period_implies_pellFSMmod_bits_period p hp N hN_eq⟩

end E213.Lib.Math.DyadicFSM.PellMatrixPigeonhole
