import E213.Math.Cohomology.Dyadic.ArithFSM.V3Equiv

/-!
# ArithFSM3.toBitFSM bits equivalence + signature period bound

Completes the cubic-class chain:
  ArithFSM3(n) bit stream = BitFSM(n³) bit stream
  ⇒ signature period ≤ 5n³.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

/-- ★★★★ ArithFSM3.toBitFSM bit stream equals original. -/
theorem toBitFSM3_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) (k : Nat) :
    (m.toBitFSM hn).bits k = m.bits k := by
  show (m.toBitFSM hn).out ((m.toBitFSM hn).run k) = m.out (m.run k)
  have hv := toBitFSM3_run_encode hn m k
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hv_isLt : ((m.toBitFSM hn).run k).val < n * n * n :=
    ((m.toBitFSM hn).run k).isLt
  have hva : ((m.toBitFSM hn).run k).val / (n * n) = (m.run k).1.val := by
    rw [hv]; exact encode3_div_nn_pub hn _ _ _
  have hvb : ((m.toBitFSM hn).run k).val % (n * n) / n = (m.run k).2.1.val := by
    rw [hv]; exact encode3_inner_div_pub hn _ _ _
  have hvc : ((m.toBitFSM hn).run k).val % n = (m.run k).2.2.val := by
    rw [hv]; exact encode3_mod_n _ _ _
  let aDec : Fin n := ⟨((m.toBitFSM hn).run k).val / (n * n), by
    have : n * n * n = n * (n * n) := Nat.mul_assoc n n n
    exact (Nat.div_lt_iff_lt_mul hnn).mpr (by omega)⟩
  let bDec : Fin n := ⟨((m.toBitFSM hn).run k).val % (n * n) / n, by
    exact (Nat.div_lt_iff_lt_mul hn).mpr (by
      have := Nat.mod_lt ((m.toBitFSM hn).run k).val hnn; omega)⟩
  let cDec : Fin n := ⟨((m.toBitFSM hn).run k).val % n, Nat.mod_lt _ hn⟩
  have hdec : (aDec, bDec, cDec)
              = ((m.run k).1, (m.run k).2.1, (m.run k).2.2) := by
    apply Prod.ext
    · exact Fin.ext hva
    · apply Prod.ext
      · exact Fin.ext hvb
      · exact Fin.ext hvc
  show m.out (aDec, bDec, cDec) = _
  rw [hdec]

/-- ★★★★★ ArithFSM3(n) signature has explicit period bound 5n³. -/
theorem arithFSM3_signature_period_bound {n : Nat} (hn : 0 < n)
    (m : ArithFSM3 n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n * n)
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k := by
  have hnnn : 0 < n * n * n := Nat.mul_pos (Nat.mul_pos hn hn) hn
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    fsm_signature_period_bound (m.toBitFSM hn) hnnn
  refine ⟨N, P, hP, hbound, ?_⟩
  intro k hk_ge
  have hbits_fn_eq : (m.toBitFSM hn).bits = m.bits :=
    funext (toBitFSM3_bits_eq hn m)
  have ⟨h_sig, _⟩ := hk k hk_ge
  rw [hbits_fn_eq] at h_sig
  exact h_sig

/-- ★★★★★★ Tribonacci mod-2 signature: explicit period bound 40 = 5·8. -/
theorem tribFSMmod2_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 40
      ∧ ∀ k, k ≥ N →
        signature tribFSMmod2.bits (k + P) = signature tribFSMmod2.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM3_signature_period_bound (n := 2) (by omega) tribFSMmod2
  exact ⟨N, P, hP, by omega, hk⟩

end E213.Math.Cohomology.Dyadic.Conjecture
