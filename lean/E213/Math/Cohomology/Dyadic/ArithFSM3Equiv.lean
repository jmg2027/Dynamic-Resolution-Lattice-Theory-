import E213.Math.Cohomology.Dyadic.ArithFSM3toBitFSM

/-!
# ArithFSM3.toBitFSM bit-stream equivalence (helpers)

Provides decode-mod-n helper and the inner-div helper used by
the run_encode and bits_eq theorems.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Encoded value modulo n recovers c. -/
theorem encode3_mod_n {n : Nat} (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) % n = c.val := by
  have hreshape : a.val * (n * n) + b.val * n + c.val
                  = (a.val * n + b.val) * n + c.val := by
    have h1 : a.val * (n * n) = a.val * n * n := by
      rw [Nat.mul_assoc]
    rw [h1, Nat.add_mul]
  rw [hreshape, Nat.add_comm _ c.val, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt c.isLt]

/-- Encoded value's mod-n² block recovers b*n + c. -/
theorem encode3_mod_nn_pub {n : Nat} (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) % (n * n) = b.val * n + c.val := by
  have hbcs : b.val * n + c.val < n * n := by
    have hb : b.val + 1 ≤ n := b.isLt
    have hc : c.val < n := c.isLt
    have hsucc : (b.val + 1) * n = b.val * n + n := Nat.succ_mul _ _
    have hbound : (b.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hb
    omega
  rw [Nat.add_assoc, Nat.mul_comm a.val (n * n), Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbcs]

/-- Encoded value's div-n² block recovers a. -/
theorem encode3_div_nn_pub {n : Nat} (hn : 0 < n) (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) / (n * n) = a.val := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hbcs : b.val * n + c.val < n * n := by
    have hb : b.val + 1 ≤ n := b.isLt
    have hc : c.val < n := c.isLt
    have hsucc : (b.val + 1) * n = b.val * n + n := Nat.succ_mul _ _
    have hbound : (b.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hb
    omega
  rw [Nat.add_assoc, Nat.mul_comm a.val (n * n), Nat.add_comm,
      Nat.add_mul_div_left _ _ hnn, Nat.div_eq_of_lt hbcs, Nat.zero_add]

/-- Inner mod/div recovers b. -/
theorem encode3_inner_div_pub {n : Nat} (hn : 0 < n) (a b c : Fin n) :
    ((a.val * (n * n) + b.val * n + c.val) % (n * n)) / n = b.val := by
  rw [encode3_mod_nn_pub a b c, Nat.mul_comm b.val n, Nat.add_comm,
      Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt c.isLt, Nat.zero_add]

/-- ★★★ ArithFSM3.toBitFSM run agrees with original (under triple-encoding). -/
theorem toBitFSM3_run_encode {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) (k : Nat) :
    ((m.toBitFSM hn).run k).val
      = (m.run k).1.val * (n * n) + (m.run k).2.1.val * n + (m.run k).2.2.val := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show ((m.toBitFSM hn).step ((m.toBitFSM hn).run k')).val = _
    have hnn : 0 < n * n := Nat.mul_pos hn hn
    have hv_isLt : ((m.toBitFSM hn).run k').val < n * n * n :=
      ((m.toBitFSM hn).run k').isLt
    have hva : ((m.toBitFSM hn).run k').val / (n * n) = (m.run k').1.val := by
      rw [ih]; exact encode3_div_nn_pub hn _ _ _
    have hvb : ((m.toBitFSM hn).run k').val % (n * n) / n = (m.run k').2.1.val := by
      rw [ih]; exact encode3_inner_div_pub hn _ _ _
    have hvc : ((m.toBitFSM hn).run k').val % n = (m.run k').2.2.val := by
      rw [ih]; exact encode3_mod_n _ _ _
    let aDec : Fin n := ⟨((m.toBitFSM hn).run k').val / (n * n), by
      have : n * n * n = n * (n * n) := Nat.mul_assoc n n n
      exact (Nat.div_lt_iff_lt_mul hnn).mpr (by omega)⟩
    let bDec : Fin n := ⟨((m.toBitFSM hn).run k').val % (n * n) / n, by
      exact (Nat.div_lt_iff_lt_mul hn).mpr (by
        have := Nat.mod_lt ((m.toBitFSM hn).run k').val hnn; omega)⟩
    let cDec : Fin n := ⟨((m.toBitFSM hn).run k').val % n, Nat.mod_lt _ hn⟩
    have hdec : (aDec, bDec, cDec)
                = ((m.run k').1, (m.run k').2.1, (m.run k').2.2) := by
      apply Prod.ext
      · exact Fin.ext hva
      · apply Prod.ext
        · exact Fin.ext hvb
        · exact Fin.ext hvc
    show (let p := m.step (aDec, bDec, cDec);
          p.1.val * (n * n) + p.2.1.val * n + p.2.2.val) = _
    rw [hdec]
    rfl

end E213.Math.Cohomology.DyadicConjecture
