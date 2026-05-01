import E213.Math.Cohomology.Dyadic.ArithFSM.V3
import E213.Math.Cohomology.Dyadic.BitFSM.Bound

/-!
# ArithFSM3(n) ⊂ BitFSM(n³) — bit-stream-faithful encoding

Encoding (a, b, c) ∈ (Fin n)³ as Fin n³ via a*n² + b*n + c.
Decode: a = v / n², b = (v % n²) / n, c = v % n.

Mirrors the ArithFSM2 → BitFSM(n²) construction, giving Tier 1
(cubic) ⊂ BitFSM at the bit-stream level.  Signature period
bound becomes 5n³.
-/

namespace E213.Math.Cohomology.Dyadic.Conjecture

private theorem encode3_bound {n : Nat} (a b c : Fin n) :
    a.val * (n * n) + b.val * n + c.val < n * n * n := by
  have ha : a.val + 1 ≤ n := a.isLt
  have hb : b.val + 1 ≤ n := b.isLt
  have hc : c.val < n := c.isLt
  have hsucc1 : (a.val + 1) * (n * n) = a.val * (n * n) + n * n :=
    Nat.succ_mul _ _
  have hsucc2 : (b.val + 1) * n = b.val * n + n := Nat.succ_mul _ _
  have hbound1 : (a.val + 1) * (n * n) ≤ n * (n * n) :=
    Nat.mul_le_mul_right (n * n) ha
  have hbound2 : (b.val + 1) * n ≤ n * n :=
    Nat.mul_le_mul_right n hb
  have hassoc : n * (n * n) = n * n * n := by
    rw [← Nat.mul_assoc]
  omega

private theorem encode3_div_nn {n : Nat} (hn : 0 < n) (a b c : Fin n) :
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

private theorem encode3_mod_nn {n : Nat} (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) % (n * n) = b.val * n + c.val := by
  have hbcs : b.val * n + c.val < n * n := by
    have hb : b.val + 1 ≤ n := b.isLt
    have hc : c.val < n := c.isLt
    have hsucc : (b.val + 1) * n = b.val * n + n := Nat.succ_mul _ _
    have hbound : (b.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hb
    omega
  rw [Nat.add_assoc, Nat.mul_comm a.val (n * n), Nat.add_comm,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbcs]

/-- ArithFSM3 encoded into BitFSM(n³) via (a, b, c) ↦ a*n² + b*n + c. -/
def ArithFSM3.toBitFSM {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) :
    BitFSM (n * n * n) where
  init := ⟨m.init.1.val * (n * n) + m.init.2.1.val * n + m.init.2.2.val, by
    have h := encode3_bound m.init.1 m.init.2.1 m.init.2.2; omega⟩
  step v :=
    let a : Fin n := ⟨v.val / (n * n), by
      have hnn : 0 < n * n := Nat.mul_pos hn hn
      have hv : v.val < n * n * n := v.isLt
      exact (Nat.div_lt_iff_lt_mul hnn).mpr (by
        have : n * n * n = n * (n * n) := Nat.mul_assoc n n n
        omega)⟩
    let b : Fin n := ⟨(v.val % (n * n)) / n, by
      have hnn : 0 < n * n := Nat.mul_pos hn hn
      have h := Nat.mod_lt v.val hnn
      exact (Nat.div_lt_iff_lt_mul hn).mpr (by
        have : n * n = n * n := rfl
        omega)⟩
    let c : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    let (a', b', c') := m.step (a, b, c)
    ⟨a'.val * (n * n) + b'.val * n + c'.val, by
      have h := encode3_bound a' b' c'; omega⟩
  out v :=
    let a : Fin n := ⟨v.val / (n * n), by
      have hnn : 0 < n * n := Nat.mul_pos hn hn
      have hv : v.val < n * n * n := v.isLt
      exact (Nat.div_lt_iff_lt_mul hnn).mpr (by
        have : n * n * n = n * (n * n) := Nat.mul_assoc n n n
        omega)⟩
    let b : Fin n := ⟨(v.val % (n * n)) / n, by
      have hnn : 0 < n * n := Nat.mul_pos hn hn
      have h := Nat.mod_lt v.val hnn
      exact (Nat.div_lt_iff_lt_mul hn).mpr (by
        have : n * n = n * n := rfl
        omega)⟩
    let c : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    m.out (a, b, c)

end E213.Math.Cohomology.Dyadic.Conjecture
