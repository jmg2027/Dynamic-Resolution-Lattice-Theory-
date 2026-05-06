import E213.Math.Cohomology.Dyadic.LCMClosure
import E213.Math.Cohomology.Dyadic.BitFSM
import E213.Math.NatHelpers.EncodePair213

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
  ⟨v.val / m, E213.Math.NatHelpers.NatDiv213.div_lt_of_lt_mul (Nat.mul_comm n m ▸ v.isLt)⟩

/-- Decode second coordinate. -/
def decodeFinSecond {n m : Nat} (hm : 0 < m) (v : Fin (n * m)) : Fin m :=
  ⟨v.val % m, Nat.mod_lt _ hm⟩

/-- Round-trip: decode first ∘ encode = first. -/
theorem decode_encode_first {n m : Nat} (hm : 0 < m)
    (a : Fin n) (b : Fin m) :
    decodeFinFirst hm (encodeFinPair a b) = a :=
  Fin.ext (E213.Math.NatHelpers.EncodePair213.encode_div hm a.val b.val b.isLt)

/-- Round-trip: decode second ∘ encode = second. -/
theorem decode_encode_second {n m : Nat} (hm : 0 < m)
    (a : Fin n) (b : Fin m) :
    decodeFinSecond hm (encodeFinPair a b) = b :=
  Fin.ext (E213.Math.NatHelpers.EncodePair213.encode_mod hm a.val b.val b.isLt)

end E213.Math.Cohomology.Dyadic.ProductHelpers
