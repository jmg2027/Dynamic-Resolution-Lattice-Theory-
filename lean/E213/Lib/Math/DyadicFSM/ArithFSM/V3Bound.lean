import E213.Lib.Math.DyadicFSM.ArithFSM.V3Equiv
import E213.Meta.Nat.NatDiv213

import E213.Lib.Math.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM
import E213.Lib.Math.DyadicFSM.BitFSM.Bound
import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# ArithFSM3.toBitFSM bits equivalence + signature period bound

Completes the cubic-class chain:
  ArithFSM3(n) bit stream = BitFSM(n³) bit stream
  ⇒ signature period ≤ 5n³.
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.V3Bound

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM
open E213.Lib.Math.DyadicFSM.ArithFSM.V3Equiv (toBitFSM3_run_encode encode3_div_nn_pub encode3_inner_div_pub encode3_mod_n)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (tribFSMmod2)
open E213.Lib.Math.DyadicFSM.BitFSM.Bound (fsm_signature_period_bound)
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature_eq_of_pointwise_eq)


/-- ★★★★ ArithFSM3.toBitFSM bit stream equals original. -/
theorem toBitFSM3_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) (k : Nat) :
    (ArithFSM3.toBitFSM hn m).bits k = m.bits k := by
  show (ArithFSM3.toBitFSM hn m).out ((ArithFSM3.toBitFSM hn m).run k) = m.out (m.run k)
  have hv := toBitFSM3_run_encode hn m k
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hv_isLt : ((ArithFSM3.toBitFSM hn m).run k).val < n * n * n :=
    ((ArithFSM3.toBitFSM hn m).run k).isLt
  have hva : ((ArithFSM3.toBitFSM hn m).run k).val / (n * n) = (m.run k).1.val := by
    rw [hv]; exact encode3_div_nn_pub hn _ _ _
  have hvb : ((ArithFSM3.toBitFSM hn m).run k).val % (n * n) / n = (m.run k).2.1.val := by
    rw [hv]; exact encode3_inner_div_pub hn _ _ _
  have hvc : ((ArithFSM3.toBitFSM hn m).run k).val % n = (m.run k).2.2.val := by
    rw [hv]; exact encode3_mod_n _ _ _
  let aDec : Fin n := ⟨((ArithFSM3.toBitFSM hn m).run k).val / (n * n),
    E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul hv_isLt⟩
  let bDec : Fin n := ⟨((ArithFSM3.toBitFSM hn m).run k).val % (n * n) / n,
    E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
      (Nat.mod_lt ((ArithFSM3.toBitFSM hn m).run k).val hnn)⟩
  let cDec : Fin n := ⟨((ArithFSM3.toBitFSM hn m).run k).val % n, Nat.mod_lt _ hn⟩
  have hdec : (aDec, bDec, cDec)
              = ((m.run k).1, (m.run k).2.1, (m.run k).2.2) := by
    apply Prod.ext
    · exact Fin.ext hva
    · apply Prod.ext
      · exact Fin.ext hvb
      · exact Fin.ext hvc
  show m.out (aDec, bDec, cDec) = _
  rw [hdec]

/-- Lift an ArithFSM3 bits-period to the encoded BitFSM via
    `toBitFSM3_bits_eq`.  G107 §4 Pell-FSM helper (ArithFSM3 analogue
    of `toBitFSM_bits_period_lift`).  PURE. -/
theorem toBitFSM3_bits_period_lift {n T : Nat} (hn : 0 < n) (m : ArithFSM3 n)
    (h : ∀ k, m.bits (k + T) = m.bits k) :
    ∀ k, (ArithFSM3.toBitFSM hn m).bits (k + T)
        = (ArithFSM3.toBitFSM hn m).bits k :=
  fun k => (toBitFSM3_bits_eq hn m (k + T)).trans
    ((h k).trans (toBitFSM3_bits_eq hn m k).symm)

/-- ★★★★★ ArithFSM3(n) signature has explicit period bound 5n³. -/
theorem arithFSM3_signature_period_bound {n : Nat} (hn : 0 < n)
    (m : ArithFSM3 n) :
    ∃ N P, 0 < P ∧ N + P ≤ 5 * (n * n * n)
      ∧ ∀ k, k ≥ N → signature m.bits (k + P) = signature m.bits k := by
  have hnnn : 0 < n * n * n := Nat.mul_pos (Nat.mul_pos hn hn) hn
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    fsm_signature_period_bound (ArithFSM3.toBitFSM hn m) hnnn
  refine ⟨N, P, hP, hbound, ?_⟩
  intro k hk_ge
  have h_pt : ∀ j, (ArithFSM3.toBitFSM hn m).bits j = m.bits j :=
    toBitFSM3_bits_eq hn m
  have ⟨h_sig, _⟩ := hk k hk_ge
  have h1 : signature (ArithFSM3.toBitFSM hn m).bits (k + P)
              = signature m.bits (k + P) :=
    signature_eq_of_pointwise_eq _ _ h_pt (k + P)
  have h2 : signature (ArithFSM3.toBitFSM hn m).bits k
              = signature m.bits k :=
    signature_eq_of_pointwise_eq _ _ h_pt k
  exact h1.symm.trans (h_sig.trans h2)

/-- ★★★★★★ Tribonacci mod-2 signature: explicit period bound 40 = 5·8. -/
theorem tribFSMmod2_signature_period_bound :
    ∃ N P, 0 < P ∧ N + P ≤ 40
      ∧ ∀ k, k ≥ N →
        signature tribFSMmod2.bits (k + P) = signature tribFSMmod2.bits k := by
  obtain ⟨N, P, hP, hbound, hk⟩ :=
    arithFSM3_signature_period_bound (n := 2) (by decide) tribFSMmod2
  exact ⟨N, P, hP, hbound, hk⟩

end E213.Lib.Math.DyadicFSM.ArithFSM.V3Bound
