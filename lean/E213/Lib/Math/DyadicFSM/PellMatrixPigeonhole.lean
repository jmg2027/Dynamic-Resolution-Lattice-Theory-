import E213.Lib.Math.DyadicFSM.PellMatrixInverse
import E213.Lib.Math.DyadicFSM.PellMatrixAction
import E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
/-!
# Existential Pisano period via pigeonhole — G119 Phase 2

Closes the existential side of the universal Pisano period theorem.

The pieces, all PURE:

  · `pellCoeff_translation` (in `PellMatrixInverse`) — any coincidence
    `pellCoeff p hp i = pellCoeff p hp j` (with `i ≤ j`) produces a
    period witness `pellCoeff p hp (j - i) = pellCoeff p hp 0`.
  · `Forward.ForwardPeriodicity.pigeonhole_collision` — constructive
    Σ-witness pigeonhole on `Fin k → Fin N` (already used by the
    signature collision argument; the underlying search functions
    avoid `Decidable.byContradiction`, which leaks propext +
    Quot.sound through instance synthesis).
  · `EncodePair213.encode_inj` (re-exposed by `ForwardPeriodicity` as
    `encode_inj`) — the pair encoding `(a, b) ↦ a · p + b` is
    injective on `[0, p) × [0, p)`.

Assembled here: `pellCoeff p hp` maps `Fin (p² + 1)` into a state
space of size `p²`, so pigeonhole forces a coincidence, and
translation yields a period `N` with `0 < N ≤ p²` and
`pellCoeff p hp N = pellCoeff p hp 0 = (⟨0,_⟩, ⟨1,_⟩)`.

The bridge `pellCoeff_period_implies_pellFSMmod_period` in
`PellMatrixAction` then lifts this to an FSM-period claim, giving:

  **∀ p > 1, ∃ N, 0 < N ≤ p² ∧ (pellFSMmod p hp).run N
                              = (pellFSMmod p hp).init.**

The G119 Phase 3 work (predictive form `N = pisano_predict p` via
FLT + legendre dispatch) remains a multi-session research direction
documented in `research-notes/G119_pisano_pell5_research_direction.md`.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.PellMatrixPigeonhole

open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.DyadicFSM.PellMatrixInverse (pellCoeff_translation)
open E213.Lib.Math.DyadicFSM.PellMatrixAction
  (pellCoeff_period_implies_pellFSMmod_period
   pellCoeff_period_implies_pellFSMmod_bits_period)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod)
open E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
  (pigeonhole_collision collTest_imp_val_eq encode_inj)
open E213.Tactic.NatHelper (sub_pos_of_lt)

/-- Pair-encode `pellCoeff p hp i.val` into `Fin (p · p)` via
    `a · p + b`.  Bound `a · p + b < p · p` from
    `a + 1 ≤ p` and `b < p`. -/
def pellEncode (p : Nat) (hp : 1 < p) (i : Fin (p * p + 1)) : Fin (p * p) :=
  ⟨(pellCoeff p hp i.val).1.val * p + (pellCoeff p hp i.val).2.val, by
    have ha : (pellCoeff p hp i.val).1.val < p := (pellCoeff p hp i.val).1.isLt
    have hb : (pellCoeff p hp i.val).2.val < p := (pellCoeff p hp i.val).2.isLt
    calc (pellCoeff p hp i.val).1.val * p + (pellCoeff p hp i.val).2.val
        < (pellCoeff p hp i.val).1.val * p + p := Nat.add_lt_add_left hb _
      _ = ((pellCoeff p hp i.val).1.val + 1) * p := (Nat.succ_mul _ p).symm
      _ ≤ p * p := Nat.mul_le_mul_right p ha⟩

/-- ★ **Existential Pisano period** for the Pell C-H coefficients.
    For every `p > 1`, the `pellCoeff p hp` sequence returns to
    `(0, 1) = pellCoeff p hp 0` in `≤ p²` steps.  PURE. -/
theorem exists_pisano_period (p : Nat) (hp : 1 < p) :
    ∃ N, 0 < N ∧ N ≤ p * p ∧ pellCoeff p hp N = pellCoeff p hp 0 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  have hlt : p * p < p * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (pellEncode p hp)
  -- `collisionTest` -> `.val` equality on the encoded outputs.
  have hval_eq : (pellEncode p hp ⟨i, hi⟩).val
                = (pellEncode p hp ⟨j, hj⟩).val :=
    collTest_imp_val_eq (pellEncode p hp) i j hi hj hcoll
  -- Pair-encode is injective on second coordinate `< p`, splitting
  -- the equality into componentwise equalities.
  have hbi : (pellCoeff p hp i).2.val < p := (pellCoeff p hp i).2.isLt
  have hbj : (pellCoeff p hp j).2.val < p := (pellCoeff p hp j).2.isLt
  obtain ⟨ha_eq, hb_eq⟩ := encode_inj hp_pos
    (pellCoeff p hp i).1.val (pellCoeff p hp j).1.val
    (pellCoeff p hp i).2.val (pellCoeff p hp j).2.val
    hbi hbj hval_eq
  -- Recover `Fin p × Fin p` equality.
  have hpc_eq : pellCoeff p hp i = pellCoeff p hp j :=
    Prod.ext (Fin.ext ha_eq) (Fin.ext hb_eq)
  -- Translation: coincidence at `(i, j)` produces period `j - i`.
  have hpt : pellCoeff p hp (j - i) = pellCoeff p hp 0 :=
    pellCoeff_translation p hp i j (Nat.le_of_lt hij) hpc_eq
  exact ⟨j - i, sub_pos_of_lt hij,
    Nat.le_trans (Nat.sub_le j i) (Nat.le_of_lt_succ hj), hpt⟩

/-- ★ **Existential FSM-period** at the (1, 1) orbit (run version):
    `pellFSMmod p hp` is periodic in `≤ p²` steps.  Bridge corollary
    of `exists_pisano_period` + `pellCoeff_period_implies_pellFSMmod_period`.
    PURE. -/
theorem exists_pellFSMmod_period (p : Nat) (hp : 1 < p) :
    ∃ N, 0 < N ∧ N ≤ p * p
      ∧ ∀ k, (pellFSMmod p hp).run (k + N) = (pellFSMmod p hp).run k := by
  obtain ⟨N, hN_pos, hN_le, hN_eq⟩ := exists_pisano_period p hp
  -- `pellCoeff p hp 0 = (⟨0, _⟩, ⟨1, _⟩)` is rfl, so `hN_eq` already has
  -- the explicit form the bridge expects.
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
