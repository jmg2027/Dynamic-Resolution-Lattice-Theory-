import E213.Lib.Math.DyadicFSM.ArithFSM.V3
import E213.Lib.Math.DyadicFSM.BitFSM.Bound
import E213.Lib.Math.NatHelpers.NatDiv213
import E213.Lib.Math.NatHelpers.EncodePair213
import E213.Term.Tactic.Nat213

import E213.Lib.Math.DyadicFSM.BitFSM
/-!
# ArithFSM3(n) ⊂ BitFSM(n³) — bit-stream-faithful encoding

Encoding (a, b, c) ∈ (Fin n)³ as Fin n³ via a*n² + b*n + c.
Decode: a = v / n², b = (v % n²) / n, c = v % n.

Mirrors the ArithFSM2 → BitFSM(n²) construction, giving Tier 1
(cubic) ⊂ BitFSM at the bit-stream level.  Signature period
bound becomes 5n³.
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.NatHelpers.NatDiv213 (div_lt_of_lt_mul)
open E213.Lib.Math.NatHelpers.EncodePair213 (encode_div encode_mod)


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
  have hassoc : n * (n * n) = n * n * n :=
    (E213.Tactic.Nat213.mul_assoc n n n).symm
  -- Goal: a.val * (n*n) + b.val * n + c.val < n*n*n
  -- bn + c < n*n by hbound2 + hc
  have hbcs : b.val * n + c.val < n * n :=
    calc b.val * n + c.val
        < b.val * n + n := Nat.add_lt_add_left hc _
      _ = (b.val + 1) * n := hsucc2.symm
      _ ≤ n * n := hbound2
  -- a*nn + (b*n + c) < a*nn + nn (with hbcs)
  have step1 : a.val * (n * n) + (b.val * n + c.val) < a.val * (n * n) + n * n :=
    Nat.add_lt_add_left hbcs _
  have step2 : a.val * (n * n) + n * n = (a.val + 1) * (n * n) := hsucc1.symm
  have step3 : (a.val + 1) * (n * n) ≤ n * n * n := hassoc ▸ hbound1
  have step4 : a.val * (n * n) + b.val * n + c.val
              = a.val * (n * n) + (b.val * n + c.val) := Nat.add_assoc _ _ _
  exact step4 ▸ Nat.lt_of_lt_of_le step1 (step2 ▸ step3)

private theorem bn_plus_c_lt_nn {n : Nat} (b c : Fin n) :
    b.val * n + c.val < n * n := by
  have hb : b.val + 1 ≤ n := b.isLt
  have hc : c.val < n := c.isLt
  have hsucc : (b.val + 1) * n = b.val * n + n := Nat.succ_mul _ _
  have hbound : (b.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n hb
  calc b.val * n + c.val
      < b.val * n + n := Nat.add_lt_add_left hc _
    _ = (b.val + 1) * n := hsucc.symm
    _ ≤ n * n := hbound

private theorem encode3_div_nn {n : Nat} (hn : 0 < n) (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) / (n * n) = a.val := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  rw [Nat.add_assoc]
  exact encode_div hnn a.val (b.val * n + c.val) (bn_plus_c_lt_nn b c)

private theorem encode3_mod_nn {n : Nat} (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) % (n * n) = b.val * n + c.val := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c.val) c.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  rw [Nat.add_assoc]
  exact encode_mod hnn a.val (b.val * n + c.val) (bn_plus_c_lt_nn b c)

/-- ArithFSM3 encoded into BitFSM(n³) via (a, b, c) ↦ a*n² + b*n + c. -/
def ArithFSM3.toBitFSM {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) :
    BitFSM (n * n * n) where
  init := ⟨m.init.1.val * (n * n) + m.init.2.1.val * n + m.init.2.2.val,
    encode3_bound m.init.1 m.init.2.1 m.init.2.2⟩
  step v :=
    let a : Fin n := ⟨v.val / (n * n), div_lt_of_lt_mul v.isLt⟩
    let b : Fin n := ⟨(v.val % (n * n)) / n,
      div_lt_of_lt_mul (Nat.mod_lt v.val (Nat.mul_pos hn hn))⟩
    let c : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    let (a', b', c') := m.step (a, b, c)
    ⟨a'.val * (n * n) + b'.val * n + c'.val, encode3_bound a' b' c'⟩
  out v :=
    let a : Fin n := ⟨v.val / (n * n), div_lt_of_lt_mul v.isLt⟩
    let b : Fin n := ⟨(v.val % (n * n)) / n,
      div_lt_of_lt_mul (Nat.mod_lt v.val (Nat.mul_pos hn hn))⟩
    let c : Fin n := ⟨v.val % n, Nat.mod_lt _ hn⟩
    m.out (a, b, c)

end E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM
