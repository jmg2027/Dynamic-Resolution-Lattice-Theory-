import E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.EncodePair213
import E213.Meta.Tactic.Fin213
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.DyadicFSM.ArithFSM.V3
/-!
# ArithFSM3.toBitFSM bit-stream equivalence (helpers)

Provides decode-mod-n helper and the inner-div helper used by
the run_encode and bits_eq theorems.
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM.V3Equiv

open E213.Lib.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)
open E213.Lib.Math.DyadicFSM.ArithFSM.V3toBitFSM


/-- 213-native `Nat.add_mul` (Lean-core leaks propext). -/
private theorem add_mul_213 : ∀ (a b c : Nat), (a + b) * c = a * c + b * c
  | _, _, 0 => rfl
  | a, b, c+1 => by
    rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, add_mul_213 a b c]
    rw [Nat.add_assoc, Nat.add_assoc (a * c)]
    congr 1
    rw [show b * c + (a + b) = (b * c + a) + b from (Nat.add_assoc _ _ _).symm,
        Nat.add_comm (b * c) a, Nat.add_assoc]

/-- Encoded value modulo n recovers c.  STRICT ∅-AXIOM. -/
theorem encode3_mod_n {n : Nat} (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) % n = c.val := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c.val) c.isLt
  have hreshape : a.val * (n * n) + b.val * n + c.val
                  = (a.val * n + b.val) * n + c.val := by
    rw [show a.val * (n * n) = a.val * n * n from
          (E213.Tactic.NatHelper.mul_assoc _ _ _).symm,
        ← add_mul_213]
  rw [hreshape]
  exact E213.Meta.Nat.EncodePair213.encode_mod hn (a.val * n + b.val) c.val c.isLt

/-- Helper: b * n + c < n * n when b, c < n.  ∅-axiom. -/
open E213.Tactic.Fin213 renaming pair_encoded_lt → bn_plus_c_lt_nn

/-- Encoded value's mod-n² block recovers b*n + c.  STRICT ∅-AXIOM. -/
theorem encode3_mod_nn_pub {n : Nat} (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) % (n * n) = b.val * n + c.val := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c.val) c.isLt
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hbcs : b.val * n + c.val < n * n := bn_plus_c_lt_nn b c
  rw [Nat.add_assoc]
  exact E213.Meta.Nat.EncodePair213.encode_mod hnn a.val (b.val * n + c.val) hbcs

/-- Encoded value's div-n² block recovers a.  STRICT ∅-AXIOM. -/
theorem encode3_div_nn_pub {n : Nat} (hn : 0 < n) (a b c : Fin n) :
    (a.val * (n * n) + b.val * n + c.val) / (n * n) = a.val := by
  have hnn : 0 < n * n := Nat.mul_pos hn hn
  have hbcs : b.val * n + c.val < n * n := bn_plus_c_lt_nn b c
  rw [Nat.add_assoc]
  exact E213.Meta.Nat.EncodePair213.encode_div hnn a.val (b.val * n + c.val) hbcs

/-- Inner mod/div recovers b.  STRICT ∅-AXIOM. -/
theorem encode3_inner_div_pub {n : Nat} (hn : 0 < n) (a b c : Fin n) :
    ((a.val * (n * n) + b.val * n + c.val) % (n * n)) / n = b.val := by
  rw [encode3_mod_nn_pub a b c]
  exact E213.Meta.Nat.EncodePair213.encode_div hn b.val c.val c.isLt

/-- ★★★ ArithFSM3.toBitFSM run agrees with original (under triple-encoding). -/
theorem toBitFSM3_run_encode {n : Nat} (hn : 0 < n) (m : ArithFSM3 n) (k : Nat) :
    ((ArithFSM3.toBitFSM hn m).run k).val
      = (m.run k).1.val * (n * n) + (m.run k).2.1.val * n + (m.run k).2.2.val := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show ((ArithFSM3.toBitFSM hn m).step ((ArithFSM3.toBitFSM hn m).run k')).val = _
    have hnn : 0 < n * n := Nat.mul_pos hn hn
    have hv_isLt : ((ArithFSM3.toBitFSM hn m).run k').val < n * n * n :=
      ((ArithFSM3.toBitFSM hn m).run k').isLt
    have hva : ((ArithFSM3.toBitFSM hn m).run k').val / (n * n) = (m.run k').1.val := by
      rw [ih]; exact encode3_div_nn_pub hn _ _ _
    have hvb : ((ArithFSM3.toBitFSM hn m).run k').val % (n * n) / n = (m.run k').2.1.val := by
      rw [ih]; exact encode3_inner_div_pub hn _ _ _
    have hvc : ((ArithFSM3.toBitFSM hn m).run k').val % n = (m.run k').2.2.val := by
      rw [ih]; exact encode3_mod_n _ _ _
    let aDec : Fin n := ⟨((ArithFSM3.toBitFSM hn m).run k').val / (n * n),
      E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul hv_isLt⟩
    let bDec : Fin n := ⟨((ArithFSM3.toBitFSM hn m).run k').val % (n * n) / n,
      E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul
        (Nat.mod_lt ((ArithFSM3.toBitFSM hn m).run k').val hnn)⟩
    let cDec : Fin n := ⟨((ArithFSM3.toBitFSM hn m).run k').val % n, Nat.mod_lt _ hn⟩
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

end E213.Lib.Math.DyadicFSM.ArithFSM.V3Equiv
