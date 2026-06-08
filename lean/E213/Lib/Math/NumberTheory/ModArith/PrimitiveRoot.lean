import E213.Lib.Math.NumberTheory.ModArith.EveryOrdDvdMax
import E213.Lib.Math.NumberTheory.ModArith.EulerConverse
import E213.Lib.Math.NumberTheory.PolyRoot.CyclotomicPoly
import E213.Lib.Math.NumberTheory.PolyRoot.RootBound
import E213.Meta.Int213.PolyIntMTactic

/-!
# PrimitiveRoot — primitive-root existence (marathon brick 5)

`maxOrd p = p − 1` and a **primitive root** exists.  Every unit `x` satisfies `x^maxOrd ≡ 1`
(`every_ord_dvd_maxOrd`), so the `p−1` units are pairwise-distinct roots of `X^maxOrd − 1`
(length `maxOrd+1`); if `maxOrd + 1 ≤ p − 1`, `RootBound.eval_zero` forces the constant
coefficient `−1 ≡ 0 (mod p)`, impossible.  Hence `p − 1 ≤ maxOrd ≤ p − 1`.

  * ★★★★ `exists_primitive_root` — `∃ g, 1 ≤ g ∧ g ≤ p−1 ∧ ordModP g p = p − 1`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP ord_pos pow_ord)
open E213.Lib.Math.NumberTheory.ModArith.EveryOrdDvdMax (every_ord_dvd_maxOrd)
open E213.Lib.Math.NumberTheory.ModArith.MaxOrder
  (maxOrd maxOrd_le_pred maxOrd_achieved one_le_maxOrd)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (pow_mul_loc)
open E213.Meta.Nat.ModPow213 (pow_mod_base)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (natCast_sub)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_pow natCast_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (dvd_sub_one_of_mod_one one_le_pow')
open E213.Lib.Math.NumberTheory.PolyRoot
  (eval nat_dvd_to_int int_dvd_to_nat pmoSucc eval_pmoSucc pmoSucc_length eval_pmoSucc_zero eval_zero)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-! ## §1 — `x^maxOrd ≡ 1` for every unit -/

/-- Every unit `x` satisfies `x^(maxOrd p) ≡ 1`: `ord x ∣ maxOrd`, so `x^maxOrd = (x^ord x)^c ≡ 1`. -/
theorem pow_maxOrd_eq_one (p x : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hx1 : 1 ≤ x) (hxp : x ≤ p - 1) : x ^ (maxOrd p) % p = 1 := by
  have hp1lt : p - 1 < p := Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one
  have hxlt : x < p := Nat.lt_of_le_of_lt hxp hp1lt
  obtain ⟨c, hc⟩ := every_ord_dvd_maxOrd p hp hpr x hx1 hxp
  rw [hc, pow_mul_loc x (ordModP x p) c, pow_mod_base (x ^ ordModP x p) p c,
      pow_ord x p hp hpr hx1 hxlt, Nat.one_pow]
  exact Nat.mod_eq_of_lt hp

/-! ## §2 — the units list `[1, …, p−1]` over `ℤ` -/

/-- `[↑lo, ↑(lo+1), …, ↑(lo+n−1)]` over `ℤ`. -/
def segInt (lo : Nat) : Nat → List Int
  | 0     => []
  | n + 1 => (lo : Int) :: segInt (lo + 1) n

theorem segInt_length (lo : Nat) : ∀ n, (segInt lo n).length = n
  | 0     => rfl
  | n + 1 => by show (segInt (lo + 1) n).length + 1 = n + 1; rw [segInt_length]

theorem mem_segInt : ∀ (n lo : Nat) {x : Int},
    x ∈ segInt lo n → ∃ i : Nat, lo ≤ i ∧ i < lo + n ∧ x = (i : Int) := by
  intro n
  induction n with
  | zero => intro lo x h; exact absurd h (List.not_mem_nil x)
  | succ n ih =>
    intro lo x h
    have h' : x ∈ (lo : Int) :: segInt (lo + 1) n := h
    cases h' with
    | head => exact ⟨lo, Nat.le_refl lo, Nat.lt_add_of_pos_right (Nat.succ_pos n), rfl⟩
    | tail _ hm =>
      obtain ⟨i, hge, hlt, hx⟩ := ih (lo + 1) hm
      refine ⟨i, Nat.le_of_succ_le hge, ?_, hx⟩
      have e1 : (lo + 1) + n = lo + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
      rw [← e1]; exact hlt

/-- Two distinct integers in `[1, p)` differ by a non-multiple of `p`. -/
theorem int_diff_not_dvd (p i j : Nat) (hi1 : 1 ≤ i) (hij : i < j) (hjp : j < p) :
    ¬ (p : Int) ∣ ((i : Int) - (j : Int)) := by
  intro hd
  have hile : i ≤ j := Nat.le_of_lt hij
  have hnat : p ∣ ((i : Int) - (j : Int)).natAbs := int_dvd_to_nat p _ hd
  have habs : ((i : Int) - (j : Int)).natAbs = j - i := by
    have e : (i : Int) - (j : Int) = -(((j - i : Nat)) : Int) := by
      rw [natCast_sub j i hile]; ring_intZ
    rw [e, Int.natAbs_neg, Int.natAbs_ofNat]
  rw [habs] at hnat
  have hpos : 0 < j - i := by
    obtain ⟨e, he⟩ := Nat.le.dest hile
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · exfalso; rw [h0, Nat.add_zero] at he; exact Nat.lt_irrefl i (he ▸ hij)
      · exact h0
    rw [← he, Nat.add_comm i e, add_sub_cancel_right]; exact he1
  exact absurd (le_of_dvd_pos p (j - i) hpos hnat)
    (Nat.not_le.mpr (Nat.lt_of_le_of_lt (Nat.sub_le j i) hjp))

/-- `[1, …, p−1]` is pairwise-distinct mod `p`. -/
theorem segInt_pairwise (p : Nat) (hp : 1 < p) :
    ∀ (n lo : Nat), 1 ≤ lo → lo + n ≤ p →
      (segInt lo n).Pairwise (fun a b => ¬ (p : Int) ∣ (a - b)) := by
  intro n
  induction n with
  | zero => intro lo _ _; exact List.Pairwise.nil
  | succ n ih =>
    intro lo hlo hbound
    have hshow : segInt lo (n + 1) = (lo : Int) :: segInt (lo + 1) n := rfl
    rw [hshow]
    have e1 : (lo + 1) + n = lo + (n + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 n]
    refine List.pairwise_cons.mpr ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨j, hjge, hjlt, hyj⟩ := mem_segInt n (lo + 1) hy
      have hloj : lo < j := Nat.lt_of_lt_of_le (Nat.lt_succ_self lo) hjge
      have hjp : j < p := Nat.lt_of_lt_of_le (e1 ▸ hjlt) hbound
      rw [hyj]; exact int_diff_not_dvd p lo j hlo hloj hjp
    · exact ih (lo + 1) (Nat.le_succ_of_le hlo) (by rw [e1]; exact hbound)

/-- Each unit is a root of `X^maxOrd − 1`. -/
theorem segInt_roots (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ r ∈ segInt 1 (p - 1), (p : Int) ∣ eval (pmoSucc (maxOrd p - 1)) r := by
  intro r hr
  obtain ⟨i, hi1, hilt, hri⟩ := mem_segInt (p - 1) 1 hr
  have hip : i ≤ p - 1 := Nat.le_of_lt_succ (by rw [Nat.add_comm] at hilt; exact hilt)
  have hmaxeq : (maxOrd p - 1) + 1 = maxOrd p := E213.Tactic.NatHelper.sub_add_cancel (one_le_maxOrd p hp hpr)
  have hpm : i ^ maxOrd p % p = 1 := pow_maxOrd_eq_one p i hp hpr hi1 hip
  rw [hri, eval_pmoSucc, hmaxeq, ← natCast_pow i (maxOrd p),
      ← natCast_sub_one (i ^ maxOrd p) (one_le_pow' i hi1 (maxOrd p))]
  exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact dvd_sub_one_of_mod_one p (i ^ maxOrd p) hpm)

/-! ## §3 — `maxOrd = p − 1` and the primitive root -/

/-- ★★★ **`maxOrd p = p − 1`.** -/
theorem maxOrd_eq_pred (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    maxOrd p = p - 1 := by
  have hle : maxOrd p ≤ p - 1 := maxOrd_le_pred p hp hpr
  refine Nat.le_antisymm hle ?_
  -- p - 1 ≤ maxOrd:  else maxOrd + 1 ≤ p - 1, and eval_zero forces -1 ≡ 0
  rcases Nat.lt_or_ge (maxOrd p) (p - 1) with hlt | hge
  · exfalso
    have hlen : (pmoSucc (maxOrd p - 1)).length ≤ (segInt 1 (p - 1)).length := by
      rw [pmoSucc_length, segInt_length]
      have hmaxeq : (maxOrd p - 1) + 2 = maxOrd p + 1 := by
        rw [show (maxOrd p - 1) + 2 = ((maxOrd p - 1) + 1) + 1 from rfl,
            E213.Tactic.NatHelper.sub_add_cancel (one_le_maxOrd p hp hpr)]
      rw [hmaxeq]; exact hlt
    have hpw := segInt_pairwise p hp (p - 1) 1 (Nat.le_refl 1) (by
      rw [Nat.add_comm 1 (p - 1)]
      exact Nat.le_of_eq (E213.Tactic.NatHelper.sub_add_cancel (Nat.le_of_lt hp)))
    have hvanish := eval_zero p hp hpr (pmoSucc (maxOrd p - 1)).length (pmoSucc (maxOrd p - 1))
      (Nat.le_refl _) (segInt 1 (p - 1)) hpw (segInt_roots p hp hpr) hlen 0
    rw [eval_pmoSucc_zero] at hvanish
    have hd1 : p ∣ Int.natAbs (-1) := int_dvd_to_nat p (-1) hvanish
    exact absurd (le_of_dvd_pos p (Int.natAbs (-1)) (by decide) hd1) (Nat.not_le.mpr hp)
  · exact hge

/-- ★★★★ **A primitive root exists.**  `∃ g, 1 ≤ g ∧ g ≤ p−1 ∧ ordModP g p = p − 1`. -/
theorem exists_primitive_root (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∃ g, 1 ≤ g ∧ g ≤ p - 1 ∧ ordModP g p = p - 1 := by
  obtain ⟨g, hg1, hgp, hgmax⟩ := maxOrd_achieved p hp
  exact ⟨g, hg1, hgp, by rw [hgmax]; exact maxOrd_eq_pred p hp hpr⟩

end E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot
