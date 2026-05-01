import E213.Math.Cohomology.Dyadic.LCMClosure
import E213.Math.Cohomology.Dyadic.BitFSM

/-!
# Generic Fin pair encoding (Fin n × Fin m ↔ Fin (n * m))

Generalises the ArithFSM2 encoding to asymmetric (n, m).
Used to define BitFSM.product across two BitFSMs of different sizes.
-/

namespace E213.Math.Cohomology.Dyadic.ProductHelpers

/-- Encode pair `(a, b) : Fin n × Fin m` into `Fin (n * m)`. -/
def encodeFinPair {n m : Nat} (a : Fin n) (b : Fin m) : Fin (n * m) :=
  ⟨a.val * m + b.val, by
    have ha : a.val + 1 ≤ n := a.isLt
    have hb : b.val < m := b.isLt
    have step1 : a.val * m + b.val < a.val * m + m :=
      Nat.add_lt_add_left hb _
    have step2 : a.val * m + m = (a.val + 1) * m :=
      (Nat.succ_mul a.val m).symm
    have step3 : (a.val + 1) * m ≤ n * m :=
      Nat.mul_le_mul_right m ha
    exact Nat.lt_of_lt_of_le step1 (step2 ▸ step3)⟩

/-- Decode first coordinate. -/
def decodeFinFirst {n m : Nat} (hm : 0 < m) (v : Fin (n * m)) : Fin n :=
  ⟨v.val / m, (Nat.div_lt_iff_lt_mul hm).mpr v.isLt⟩

/-- Decode second coordinate. -/
def decodeFinSecond {n m : Nat} (hm : 0 < m) (v : Fin (n * m)) : Fin m :=
  ⟨v.val % m, Nat.mod_lt _ hm⟩

/-- Round-trip: decode first ∘ encode = first. -/
theorem decode_encode_first {n m : Nat} (hm : 0 < m)
    (a : Fin n) (b : Fin m) :
    decodeFinFirst hm (encodeFinPair a b) = a := by
  apply Fin.ext
  show (a.val * m + b.val) / m = a.val
  rw [Nat.mul_comm a.val m, Nat.add_comm, Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt b.isLt, Nat.zero_add]

/-- Round-trip: decode second ∘ encode = second. -/
theorem decode_encode_second {n m : Nat} (hm : 0 < m)
    (a : Fin n) (b : Fin m) :
    decodeFinSecond hm (encodeFinPair a b) = b := by
  apply Fin.ext
  show (a.val * m + b.val) % m = b.val
  rw [Nat.mul_comm a.val m, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt b.isLt]

end E213.Math.Cohomology.Dyadic.ProductHelpers
