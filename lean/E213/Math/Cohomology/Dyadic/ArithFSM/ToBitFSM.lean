import E213.Math.Cohomology.Dyadic.ArithFSM.Mod5
import E213.Math.Cohomology.Dyadic.BitFSM.Bound

/-!
# ArithFSM2(n) ⊂ BitFSM(n²) — bit-stream equivalence

`ArithFSM2.toBitFSM` encodes the (Fin n × Fin n) state as a single
Fin n² value via `a * n + b`.  Decoding via `/n` and `% n` is exact.

Consequence: every ArithFSM2(n) bit stream is BitFSM(n²)-generable,
hence its K_{3,2}^{(2)} signature is eventually periodic with
explicit period ≤ 5n² (via `fsm_signature_period_bound`).
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

private theorem encode_div {n : Nat} (hn : 0 < n) (a b : Fin n) :
    (a.val * n + b.val) / n = a.val := by
  rw [Nat.mul_comm a.val n, Nat.add_comm, Nat.add_mul_div_left _ _ hn,
      Nat.div_eq_of_lt b.isLt, Nat.zero_add]

private theorem encode_mod {n : Nat} (a b : Fin n) :
    (a.val * n + b.val) % n = b.val := by
  rw [Nat.mul_comm a.val n, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b.isLt]

/-- ArithFSM2.toBitFSM run agrees with original (under pair-encoding). -/
theorem toBitFSM_run_encode {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat) :
    ((m.toBitFSM hn).run k).val
      = (m.run k).1.val * n + (m.run k).2.val := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show ((m.toBitFSM hn).step ((m.toBitFSM hn).run k')).val = _
    have hv_isLt : ((m.toBitFSM hn).run k').val < n * n :=
      ((m.toBitFSM hn).run k').isLt
    have hva : ((m.toBitFSM hn).run k').val / n = (m.run k').1.val := by
      rw [ih]; exact encode_div hn _ _
    have hvb : ((m.toBitFSM hn).run k').val % n = (m.run k').2.val := by
      rw [ih]; exact encode_mod _ _
    let aDec : Fin n :=
      ⟨((m.toBitFSM hn).run k').val / n,
       (Nat.div_lt_iff_lt_mul hn).mpr hv_isLt⟩
    let bDec : Fin n :=
      ⟨((m.toBitFSM hn).run k').val % n, Nat.mod_lt _ hn⟩
    have hdec : (aDec, bDec) = ((m.run k').1, (m.run k').2) := by
      apply Prod.ext
      · exact Fin.ext hva
      · exact Fin.ext hvb
    show (let p := m.step (aDec, bDec); p.1.val * n + p.2.val) = _
    rw [hdec]
    rfl

/-- ★★★★ ArithFSM2.toBitFSM bit stream equals original bit stream. -/
theorem toBitFSM_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat) :
    (m.toBitFSM hn).bits k = m.bits k := by
  show (m.toBitFSM hn).out ((m.toBitFSM hn).run k) = m.out (m.run k)
  have hv := toBitFSM_run_encode hn m k
  have hv_isLt : ((m.toBitFSM hn).run k).val < n * n :=
    ((m.toBitFSM hn).run k).isLt
  have hva : ((m.toBitFSM hn).run k).val / n = (m.run k).1.val := by
    rw [hv]; exact encode_div hn _ _
  have hvb : ((m.toBitFSM hn).run k).val % n = (m.run k).2.val := by
    rw [hv]; exact encode_mod _ _
  let aDec : Fin n :=
    ⟨((m.toBitFSM hn).run k).val / n,
     (Nat.div_lt_iff_lt_mul hn).mpr hv_isLt⟩
  let bDec : Fin n :=
    ⟨((m.toBitFSM hn).run k).val % n, Nat.mod_lt _ hn⟩
  have hdec : (aDec, bDec) = ((m.run k).1, (m.run k).2) := by
    apply Prod.ext
    · exact Fin.ext hva
    · exact Fin.ext hvb
  show m.out (aDec, bDec) = _
  rw [hdec]

/-- ★★★★★ ArithFSM2(n) signature has explicit period bound 5n².
    Strict-zero axiom (uses signature_eq_of_pointwise_eq instead of funext). -/
theorem arithFSM2_signature_period_bound {n : Nat} (hn : 0 < n)
    (m : ArithFSM2 n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n)
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    fsm_signature_period_bound (m.toBitFSM hn) hnn
  refine ⟨N, P, hP, hbound, ?_⟩
  intro k hk_ge
  have h_pt : ∀ j, (m.toBitFSM hn).bits j = m.bits j := toBitFSM_bits_eq hn m
  have ⟨h_sig, _⟩ := hk k hk_ge
  -- h_sig : signature (m.toBitFSM hn).bits (k+P) = signature (m.toBitFSM hn).bits k
  -- Use pointwise equality lemma (strict-zero axiom) instead of funext.
  have h1 : signature (m.toBitFSM hn).bits (k + P) = signature m.bits (k + P) :=
    signature_eq_of_pointwise_eq _ _ h_pt (k + P)
  have h2 : signature (m.toBitFSM hn).bits k = signature m.bits k :=
    signature_eq_of_pointwise_eq _ _ h_pt k
  exact h1.symm.trans (h_sig.trans h2)

/-- ★★★★★★ Pell mod-5 signature: explicit period bound 125 = 5·25. -/
theorem pellFSMmod5_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 125
      ∧ ∀ k, k ≥ N →
        signature pellFSMmod5.bits (k + P) = signature pellFSMmod5.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM2_signature_period_bound (n := 5) (by omega) pellFSMmod5
  exact ⟨N, P, hP, by omega, hk⟩

end E213.Math.Cohomology.Dyadic.Conjecture
