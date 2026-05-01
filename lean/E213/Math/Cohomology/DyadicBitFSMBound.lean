import E213.Math.Cohomology.DyadicBitFSM

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

namespace E213.Math.Cohomology.DyadicConjecture

/-- Joint state (signature, run) at step k, encoded into Fin (5n). -/
def fsmJointAt {n : Nat} (m : BitFSM n) (hn : 0 < n) (k : Fin (5 * n + 1))
    : Fin (5 * n) :=
  ⟨(signature m.bits k.val).val * n + (m.run k.val).val, by
    have h1 : (signature m.bits k.val).val < 5 :=
      (signature m.bits k.val).isLt
    have h2 : (m.run k.val).val < n := (m.run k.val).isLt
    have h3 : (signature m.bits k.val).val * n ≤ 4 * n :=
      Nat.mul_le_mul_right n (by omega)
    omega⟩

/-- ★ Joint (sig, run) collision via pigeonhole. -/
theorem fsm_joint_collision {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ i, i ≤ 5 * n ∧ ∃ j, j ≤ 5 * n ∧ i < j
      ∧ signature m.bits i = signature m.bits j
      ∧ m.run i = m.run j := by
  have hlt : 5 * n < 5 * n + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (fsmJointAt m hn)
  have hjs_eq : (fsmJointAt m hn ⟨i, hi⟩).val
                  = (fsmJointAt m hn ⟨j, hj⟩).val := by
    unfold collisionTest at hcoll
    simp [hi, hj] at hcoll
    omega
  have hval : (signature m.bits i).val * n + (m.run i).val
                = (signature m.bits j).val * n + (m.run j).val := hjs_eq
  have hri : (m.run i).val < n := (m.run i).isLt
  have hrj : (m.run j).val < n := (m.run j).isLt
  have hdiv_i : ((signature m.bits i).val * n + (m.run i).val) / n
                  = (signature m.bits i).val := by
    rw [Nat.mul_comm (signature m.bits i).val n, Nat.add_comm,
        Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hri, Nat.zero_add]
  have hdiv_j : ((signature m.bits j).val * n + (m.run j).val) / n
                  = (signature m.bits j).val := by
    rw [Nat.mul_comm (signature m.bits j).val n, Nat.add_comm,
        Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hrj, Nat.zero_add]
  have h_sig_eq : (signature m.bits i).val = (signature m.bits j).val := by
    rw [← hdiv_i, ← hdiv_j, hval]
  refine ⟨i, by omega, j, by omega, hij, Fin.ext h_sig_eq, ?_⟩
  have h_offset : (signature m.bits i).val * n
                    = (signature m.bits j).val * n := by rw [h_sig_eq]
  apply Fin.ext
  show (m.run i).val = (m.run j).val
  omega

/-- ★★★★★ Tight bound: BitFSM(n) signature has pre-period + period ≤ 5n. -/
theorem fsm_signature_period_bound {n : Nat} (m : BitFSM n) (hn : 0 < n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * n
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k
      ∧ m.run (k + P) = m.run k := by
  obtain ⟨i, _, j, hj, hij, hsig, hrun⟩ := fsm_joint_collision m hn
  refine ⟨i, j - i, by omega, by omega, ?_⟩
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = i + d :=
    ⟨k - i, (Nat.add_sub_cancel' hk).symm⟩
  clear hk
  induction d with
  | zero =>
    refine ⟨?_, ?_⟩
    · show signature m.bits (i + 0 + (j - i)) = signature m.bits (i + 0)
      rw [Nat.add_zero, show i + (j - i) = j by omega]; exact hsig.symm
    · show m.run (i + 0 + (j - i)) = m.run (i + 0)
      rw [Nat.add_zero, show i + (j - i) = j by omega]; exact hrun.symm
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

end E213.Math.Cohomology.DyadicConjecture
