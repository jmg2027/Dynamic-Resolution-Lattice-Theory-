import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum

/-!
# The norm element squares to `p` times itself — `N ⋆ N = p · N` (∅-axiom)

Let `Yfun p` be the coefficient function of `g·conj g = p·1 − N` (`gauss_conj_norm`):
`Yfun p k = ofInt(p−1)` if `k=0`, else `ofInt(−1)`.  Then in the group ring `R[C_p]`

  `(Yfun p ⋆ Yfun p)(n) = ofInt(↑p) · Yfun p n`   (`Yfun_conv`),

i.e. `Y² = p·Y` — **pure convolution combinatorics** (no characters).  Write `Yfun = (−1) + B`
pointwise (`B k = ofInt p` if `k=0` else `0`); expand the summand bilinearly and evaluate the four
pieces: `Σ ofInt 1 = ofInt ↑p` (`sum_ones`), two single-point sums (`sum_single`, `= ±ofInt p` shapes),
and the `B⋆B` term `= ofInt p · B n`.  The `ofInt ↑p + ofInt(−1)·ofInt ↑p = 0` cancellation leaves
`ofInt ↑p · (−1 + B n) = ofInt ↑p · Yfun n`.  Combined with the Gauss–Jacobi relation `g²=J·g(χ²)`,
this gives the Jacobi-sum norm `N(J)=p` (A3).
∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (ofInt_add ofInt_neg)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (ofInt_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sumRange_succ sum_add sum_congr sum_single)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (add_p_mod)
open E213.Meta.Nat.AddMod213 (mod_self)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel nat_add_sub_self_right)
open E213.Tactic.NatHelper (add_sub_assoc add_sub_add_right)
open E213.Meta.Algebra213.Ring213
  (mul_add add_mul mul_zero zero_mul zero_add add_comm neg_add_cancel_self)
open E213.Meta.Int213 (neg_mul)
open E213.Meta.Int213.PolyIntM (one_mulZ)

/-- The norm coefficient function `Yfun p k = ofInt(p−1)` if `k=0`, else `ofInt(−1)`. -/
def Yfun (p k : Nat) : ZOmega := if k = 0 then ofInt (((p - 1 : Nat)) : Int) else ofInt (-1)

/-- The `p·e_0` part of `Yfun`: `Bfun p k = ofInt p` if `k=0`, else `0`. -/
def Bfun (p k : Nat) : ZOmega := if k = 0 then ofInt ((p : Nat) : Int) else 0

/-- `Bfun p 0 = ofInt ↑p`. -/
private theorem Bfun_zero {p : Nat} : Bfun p 0 = ofInt ((p : Nat) : Int) := by
  unfold Bfun; rw [if_pos rfl]

/-- Pure `i < k ⟹ 0 < k − i`. -/
private theorem sub_pos_pure {i k : Nat} (h : i < k) : 0 < k - i := by
  have h2 : (i + 1) - i ≤ k - i := Nat.sub_le_sub_right (Nat.succ_le_of_lt h) i
  rwa [Nat.add_comm i 1, nat_add_sub_self_right] at h2

/-- `Σ_{i<n} ofInt 1 = ofInt ↑n` — the constant-`1` sum counts the terms.  ∅-axiom. -/
theorem sum_ones : ∀ n : Nat, sumRange (fun _ => ofInt 1) n = ofInt ((n : Nat) : Int)
  | 0 => rfl
  | n + 1 => by
      rw [sumRange_succ, sum_ones n, ofInt_add]
      rfl

/-- The decomposition `Yfun p k = ofInt(−1) + Bfun p k` (pointwise; `1 ≤ p`). -/
private theorem Y_decomp {p : Nat} (hp1 : 1 ≤ p) (k : Nat) :
    Yfun p k = ofInt (-1) + Bfun p k := by
  unfold Yfun Bfun
  by_cases hk : k = 0
  · rw [if_pos hk, if_pos hk, ofInt_add]
    congr 1
    have e1 : (((p - 1 : Nat)) : Int) + 1 = ((p : Nat) : Int) := by
      have h : (((p - 1 : Nat)) : Int) + 1 = ((((p - 1) + 1 : Nat)) : Int) := rfl
      rw [h, nat_sub_add_cancel hp1]
    rw [← e1]; ring_intZ
  · rw [if_neg hk, if_neg hk, E213.Meta.Algebra213.Ring213.add_zero]

/-- The shifted index `(n+p−i)%p` is nonzero off `i = n` (for `i, n < p`).  ∅-axiom. -/
private theorem shift_ne_zero {p n : Nat} (hppos : 0 < p) (hnp : n < p) :
    ∀ i, i < p → i ≠ n → (n + p - i) % p ≠ 0 := by
  intro i hi hne
  rcases Nat.lt_or_ge i n with hlt | hge
  · have he : n + p - i = (n - i) + p := by
      rw [Nat.add_comm n p, add_sub_assoc p (Nat.le_of_lt hlt), Nat.add_comm p (n - i)]
    rw [he, add_p_mod hppos, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le n i) hnp)]
    exact fun h => Nat.lt_irrefl 0 (h ▸ sub_pos_pure hlt)
  · have hgt : n < i := Nat.lt_of_le_of_ne hge (fun h => hne h.symm)
    have he : n + p - i = p - (i - n) := by
      rw [Nat.add_comm n p, ← add_sub_add_right p n (i - n), nat_sub_add_cancel (Nat.le_of_lt hgt)]
    have hin : i - n < p := Nat.lt_of_le_of_lt (Nat.sub_le i n) hi
    rw [he, Nat.mod_eq_of_lt (Nat.sub_lt hppos (sub_pos_pure hgt))]
    exact fun h => Nat.lt_irrefl 0 (h ▸ sub_pos_pure hin)

/-- `(n+p−n)%p = 0`. -/
private theorem shift_self {p n : Nat} : (n + p - n) % p = 0 := by
  rw [Nat.add_comm n p, nat_add_sub_self_right, mod_self]

/-- ★★★★★ **`Y ⋆ Y = p · Y`** (coefficient form) — for `1 ≤ p`, `n < p`,
    `(Yfun p ⋆ Yfun p)(n) = ofInt(↑p) · Yfun p n`.  Pure convolution combinatorics.  ∅-axiom. -/
theorem Yfun_conv {p n : Nat} (hp1 : 1 ≤ p) (hnp : n < p) :
    conv p (Yfun p) (Yfun p) n = ofInt ((p : Nat) : Int) * Yfun p n := by
  have hppos : 0 < p := hp1
  show sumRange (fun i => Yfun p i * Yfun p ((n + p - i) % p)) p = _
  -- expand each summand bilinearly:  (−1 + B i)·(−1 + B(n+p−i)) = (g1+g2)+(g3+g4)
  rw [sum_congr p (fun i _ => by
        rw [Y_decomp hp1 i, Y_decomp hp1 ((n + p - i) % p), add_mul, mul_add, mul_add])]
  rw [sum_add, sum_add, sum_add]
  -- S1 = Σ ofInt(−1)·ofInt(−1) = ofInt ↑p
  rw [show sumRange (fun i => ofInt (-1) * ofInt (-1)) p = ofInt ((p : Nat) : Int) from by
        rw [sum_congr p (fun i _ => by rw [← ofInt_mul])]; exact sum_ones p]
  -- S2 = Σ ofInt(−1)·B(n+p−i) = ofInt(−1)·ofInt ↑p   (single point i = n)
  rw [show sumRange (fun i => ofInt (-1) * Bfun p ((n + p - i) % p)) p
        = ofInt (-1) * ofInt ((p : Nat) : Int) from by
        rw [sum_single p n hnp _ (fun i hi hne => by
              show ofInt (-1) * Bfun p ((n + p - i) % p) = 0
              unfold Bfun; rw [if_neg (shift_ne_zero hppos hnp i hi hne), mul_zero])]
        show ofInt (-1) * Bfun p ((n + p - n) % p) = _
        rw [shift_self, Bfun_zero]]
  -- S3 = Σ B i·ofInt(−1) = ofInt ↑p·ofInt(−1)   (single point i = 0)
  rw [show sumRange (fun i => Bfun p i * ofInt (-1)) p
        = ofInt ((p : Nat) : Int) * ofInt (-1) from by
        rw [sum_single p 0 hppos _ (fun i hi hne => by
              show Bfun p i * ofInt (-1) = 0
              unfold Bfun; rw [if_neg hne, zero_mul])]
        show Bfun p 0 * ofInt (-1) = _
        rw [Bfun_zero]]
  -- S4 = Σ B i·B(n+p−i) = ofInt ↑p·B n   (single point i = 0)
  rw [show sumRange (fun i => Bfun p i * Bfun p ((n + p - i) % p)) p
        = ofInt ((p : Nat) : Int) * Bfun p n from by
        rw [sum_single p 0 hppos _ (fun i hi hne => by
              show Bfun p i * Bfun p ((n + p - i) % p) = 0
              unfold Bfun; rw [if_neg hne, zero_mul])]
        show Bfun p 0 * Bfun p ((n + p - 0) % p) = _
        rw [Nat.sub_zero, add_p_mod hppos n, Nat.mod_eq_of_lt hnp, Bfun_zero]]
  -- combine:  (↑p + (−1)·↑p) + (↑p·(−1) + ↑p·B n) = ↑p·Y n
  have hPMP : ofInt ((p : Nat) : Int) + ofInt (-1) * ofInt ((p : Nat) : Int) = 0 := by
    have hm : (-1 : Int) * ((p : Nat) : Int) = -((p : Nat) : Int) := by rw [neg_mul, one_mulZ]
    rw [← ofInt_mul, hm, ofInt_neg, add_comm, neg_add_cancel_self]
  rw [Y_decomp hp1 n, mul_add, hPMP, zero_add]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv
