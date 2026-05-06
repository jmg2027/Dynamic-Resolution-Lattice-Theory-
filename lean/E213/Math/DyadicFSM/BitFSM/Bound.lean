import E213.Math.DyadicFSM.BitFSM
import E213.Math.NatHelpers.EncodePair213
import E213.Kernel.Tactic.Nat213

import E213.Math.DyadicFSM.ForwardPeriodicity
import E213.Math.DyadicFSM.Signature
/-!
# Explicit signature period bound for BitFSM-generated streams

For a BitFSM with `n` states, the joint state (signature, run)
takes values in Fin (5n).  Pigeonhole forces collision within
5n+1 steps, so the signature trajectory is periodic with
explicit period ≤ 5n.

This is the *quantitative* version of `fsm_signature_eventually_periodic`:
not just "eventually periodic" but "with bounded period".

Implication: any bit stream whose signature has UNBOUNDED period
(in any sense) cannot be BitFSM-generated, regardless of state count.
This is the formal shape of "Tier 2 ⊄ BitFSM-class".
-/

namespace E213.Math.DyadicFSM.BitFSM.Bound

open E213.Math.DyadicFSM.ForwardPeriodicity
  (collisionTest pigeonhole_collision collTest_imp_val_eq encode_inj)
open E213.Math.DyadicFSM.Signature (nextVertex signature)
open E213.Math.DyadicFSM.BitFSM (BitFSM)


/-- Joint state (signature, run) at step k, encoded into Fin (5n). -/
def fsmJointAt {n : Nat} (m : BitFSM n) (hn : 0 < n) (k : Fin (5 * n + 1))
    : Fin (5 * n) :=
  ⟨(signature m.bits k.val).val * n + (m.run k.val).val, by
    have h1 : (signature m.bits k.val).val < 5 :=
      (signature m.bits k.val).isLt
    have h2 : (m.run k.val).val < n := (m.run k.val).isLt
    have h1' : (signature m.bits k.val).val ≤ 4 := Nat.lt_succ_iff.mp h1
    have h3 : (signature m.bits k.val).val * n ≤ 4 * n :=
      Nat.mul_le_mul_right n h1'
    calc (signature m.bits k.val).val * n + (m.run k.val).val
        < 4 * n + n := Nat.add_lt_add_of_le_of_lt h3 h2
      _ = (4 + 1) * n := (Nat.succ_mul 4 n).symm
      _ = 5 * n := rfl⟩

/-- ★ Joint (sig, run) collision via pigeonhole.  STRICT ∅-AXIOM. -/
theorem fsm_joint_collision {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ i, i ≤ 5 * n ∧ ∃ j, j ≤ 5 * n ∧ i < j
      ∧ signature m.bits i = signature m.bits j
      ∧ m.run i = m.run j := by
  have hlt : 5 * n < 5 * n + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (fsmJointAt m hn)
  have hval_eq : (fsmJointAt m hn ⟨i, hi⟩).val
                = (fsmJointAt m hn ⟨j, hj⟩).val :=
    collTest_imp_val_eq (fsmJointAt m hn) i j hi hj hcoll
  have hval : (signature m.bits i).val * n + (m.run i).val
              = (signature m.bits j).val * n + (m.run j).val := hval_eq
  have hri : (m.run i).val < n := (m.run i).isLt
  have hrj : (m.run j).val < n := (m.run j).isLt
  obtain ⟨h_sig_eq, h_run_eq⟩ :=
    encode_inj hn (signature m.bits i).val (signature m.bits j).val
      (m.run i).val (m.run j).val hri hrj hval
  exact ⟨i, Nat.lt_succ_iff.mp hi, j, Nat.lt_succ_iff.mp hj, hij,
         Fin.ext h_sig_eq, Fin.ext h_run_eq⟩

/-- ∅-axiom replacement for `Nat.sub_pos_of_lt` (which leaks propext). -/
private theorem sub_pos_of_lt_213 : ∀ {a b : Nat}, a < b → 0 < b - a
  | 0, _, h => by rw [Nat.sub_zero]; exact h
  | k+1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | k+1, m+1, h => by
    rw [Nat.succ_sub_succ_eq_sub]
    exact sub_pos_of_lt_213 (Nat.lt_of_succ_lt_succ h)

/-- ★★★★★ Tight bound: BitFSM(n) signature has pre-period + period ≤ 5n.
    STRICT ∅-AXIOM via 213-native helpers (no omega / no Nat.add_sub_cancel'). -/
theorem fsm_signature_period_bound {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * n
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k
      ∧ m.run (k + P) = m.run k := by
  obtain ⟨i, hi, j, hj, hij, hsig, hrun⟩ := fsm_joint_collision m hn
  have hP : 0 < j - i := sub_pos_of_lt_213 hij
  have hi_le_j : i ≤ j := Nat.le_of_lt hij
  have hbound : i + (j - i) ≤ 5 * n :=
    Nat.le_trans
      (Nat.le_of_eq (E213.Tactic.Nat213.add_sub_of_le hi_le_j)) hj
  refine ⟨i, j - i, hP, hbound, ?_⟩
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d :=
    ⟨k - i, (E213.Tactic.Nat213.add_sub_of_le hk).symm⟩
  clear hk
  have hij_eq : i + (j - i) = j := E213.Tactic.Nat213.add_sub_of_le hi_le_j
  induction d with
  | zero =>
    refine ⟨?_, ?_⟩
    · show signature m.bits (i + 0 + (j - i)) = signature m.bits (i + 0)
      rw [Nat.add_zero, hij_eq]; exact hsig.symm
    · show m.run (i + 0 + (j - i)) = m.run (i + 0)
      rw [Nat.add_zero, hij_eq]; exact hrun.symm
  | succ d' ih =>
    obtain ⟨ih_sig, ih_run⟩ := ih
    have h1 : i + (d' + 1) + (j - i) = (i + d' + (j - i)) + 1 :=
      Nat.succ_add (i + d') (j - i)
    have h2 : i + (d' + 1) = (i + d') + 1 := rfl
    refine ⟨?_, ?_⟩
    · rw [h1, h2]
      show nextVertex (signature m.bits (i + d' + (j - i)))
              (m.bits (i + d' + (j - i)))
        = nextVertex (signature m.bits (i + d')) (m.bits (i + d'))
      rw [ih_sig]
      show nextVertex _ (m.out (m.run (i + d' + (j - i))))
        = nextVertex _ (m.out (m.run (i + d')))
      rw [ih_run]
    · rw [h1, h2]
      show m.step (m.run (i + d' + (j - i))) = m.step (m.run (i + d'))
      rw [ih_run]

end E213.Math.DyadicFSM.BitFSM.Bound
