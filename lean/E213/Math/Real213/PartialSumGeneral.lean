import E213.Kernel.Tactic.Nat213
import E213.Math.Real213.CutSeries
import E213.Math.Real213.CutSumGeneral

/-!
# Real213PartialSumGeneral — partialSum of constant cut at any denom

Generalises `partialSum_const_int` (b=1) and `partialSum_const_half`
(b=2) to ARBITRARY denominator b ≥ 1, in the forward direction.

## What was missing

The existing closed-form theorems are limited to b ∈ {1, 2}:
  partialSum_const_int  : Σ_{i<n} a/1 = (n*a)/1   (equality, b=1)
  partialSum_const_half : Σ_{i<n+1} a/2 = (n+1)·a/2  (equality, b=2)

At b ≥ 3, the precision artifact in cutSum prevents a clean
equality.  But the FORWARD direction (one-sided bound) holds at
ANY b.

## What's now proved

  partialSum_const_b_forward (a b n m k):
    partialSum (fun _ => constCut a b) n m k = true
      ⇒ constCut (n * a) b m k = true.
-/

namespace E213.Math.Real213.PartialSumGeneral

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Math.Real213.CutSumComm (cutSumAux_eq_true_iff)
open E213.Math.Real213.CutSumTest (constCut)

/-- ★★★★★★ partialSum of constant cut, forward direction at any b. -/
theorem partialSum_const_b_forward (a b : Nat) :
    ∀ n m k, partialSum (fun _ => constCut a b) n m k = true →
             constCut (n * a) b m k = true := by
  intro n
  induction n with
  | zero =>
    intro m k _
    show decide (0 * a * k ≤ b * m) = true
    apply decide_eq_true
    rw [Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _
  | succ n ih =>
    intro m k h
    change cutSum (partialSum (fun _ => constCut a b) n)
                  (constCut a b) m k = true at h
    change cutSumAux (partialSum (fun _ => constCut a b) n)
                  (constCut a b) k (2*m) (2*m) = true at h
    rw [cutSumAux_eq_true_iff] at h
    obtain ⟨i, _, h_psn, h_cb⟩ := h
    have h_ind : constCut (n * a) b i (2 * k) = true := ih i (2*k) h_psn
    have h_n : (n * a) * (2 * k) ≤ b * i := of_decide_eq_true h_ind
    have h_a : a * (2 * k) ≤ b * (2 * m - i) := of_decide_eq_true h_cb
    show decide ((n + 1) * a * k ≤ b * m) = true
    apply decide_eq_true
    have h_add : (n*a)*(2*k) + a*(2*k) ≤ b*i + b*(2*m - i) :=
      Nat.add_le_add h_n h_a
    have h_rhs : b * i + b * (2 * m - i) = b * (2 * m) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [h_rhs] at h_add
    have h_lhs : (n*a)*(2*k) + a*(2*k) = 2 * ((n+1) * a * k) := by
      have e1 : (n*a)*(2*k) = 2*((n*a)*k) := by
        rw [Nat.mul_comm (n*a), E213.Tactic.Nat213.mul_assoc, Nat.mul_comm k]
      have e2 : a*(2*k) = 2*(a*k) := by
        rw [Nat.mul_comm a, E213.Tactic.Nat213.mul_assoc, Nat.mul_comm k]
      have e3 : (n+1) * a * k = (n*a)*k + a*k := by
        rw [Nat.succ_mul n a, Nat.add_mul]
      omega
    have h_rhs2 : b * (2 * m) = 2 * (b * m) := by
      rw [Nat.mul_comm b, E213.Tactic.Nat213.mul_assoc, Nat.mul_comm m]
    rw [h_lhs, h_rhs2] at h_add
    exact Nat.le_of_mul_le_mul_left h_add (by decide : 0 < 2)

/-- Sum of n thirds: forward direction at b=3 (previously blocked). -/
theorem partialSum_thirds_forward (n m k : Nat) :
    partialSum (fun _ => constCut 1 3) n m k = true →
    constCut n 3 m k = true := by
  intro h
  have := partialSum_const_b_forward 1 3 n m k h
  rwa [Nat.mul_one] at this

/-- Sum of n fifths: forward direction at b=5 (previously blocked). -/
theorem partialSum_fifths_forward (n m k : Nat) :
    partialSum (fun _ => constCut 1 5) n m k = true →
    constCut n 5 m k = true := by
  intro h
  have := partialSum_const_b_forward 1 5 n m k h
  rwa [Nat.mul_one] at this

end E213.Math.Real213.PartialSumGeneral
