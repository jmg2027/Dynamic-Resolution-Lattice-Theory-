import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# `odd_central_binom_le : C(2m+1, m) ≤ 4^m` (∅-axiom)

The sharp bound on the odd central binomial — the second Bertrand keystone (after the
primorial bound).  The two equal middle terms of row `2m+1` of Pascal's triangle
(`choose_symm`: `C(2m+1,m) = C(2m+1,m+1)`) sum to `≤ Σ_k C(2m+1,k) = 2^{2m+1}`
(`pascal_row_sum`), so `2·C(2m+1,m) ≤ 2^{2m+1} = 2·4^m`.
-/

namespace E213.Lib.Math.NumberTheory.OddCentralBinom

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_symm)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (pascal_row_sum)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- A single term is `≤` the sum (all terms `≥ 0` in ℕ). -/
theorem term_le_sumTo (f : Nat → Nat) : ∀ {n i : Nat}, i < n → f i ≤ sumTo n f := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
      intro i hi
      rw [sumTo_succ]
      rcases Nat.lt_or_ge i k with hik | hik
      · exact Nat.le_trans (ih hik) (Nat.le_add_right _ _)
      · have hik' : i = k := Nat.le_antisymm (Nat.le_of_lt_succ hi) hik
        subst hik'
        exact Nat.le_add_left (f i) (sumTo i f)

/-- The sum is monotone in its length (terms `≥ 0`). -/
theorem sumTo_mono_len (f : Nat → Nat) : ∀ {m n : Nat}, m ≤ n → sumTo m f ≤ sumTo n f := by
  intro m n
  induction n with
  | zero => intro h; have : m = 0 := Nat.le_antisymm h (Nat.zero_le m); subst this; exact Nat.le_refl _
  | succ k ih =>
      intro h
      rcases Nat.lt_or_ge m (k + 1) with hm | hm
      · rw [sumTo_succ]; exact Nat.le_trans (ih (Nat.le_of_lt_succ hm)) (Nat.le_add_right _ _)
      · have : m = k + 1 := Nat.le_antisymm h hm; subst this; exact Nat.le_refl _

/-- Two distinct terms are `≤` the sum. -/
theorem two_terms_le_sumTo (f : Nat → Nat) {n i j : Nat} (hij : i < j) (hjn : j < n) :
    f i + f j ≤ sumTo n f :=
  calc f i + f j ≤ sumTo j f + f j := Nat.add_le_add_right (term_le_sumTo f hij) (f j)
    _ = sumTo (j + 1) f := (sumTo_succ j f).symm
    _ ≤ sumTo n f := sumTo_mono_len f hjn

/-- `4^m = 2^{2m}` (pure induction, avoiding the propext-tainted `Nat.pow_mul`). -/
theorem four_pow_eq : ∀ m, (4 : Nat) ^ m = 2 ^ (2 * m)
  | 0     => rfl
  | m + 1 => by
      have ih := four_pow_eq m
      rw [Nat.pow_succ, ih, show 2 * (m + 1) = (2 * m) + 1 + 1 from by ring_nat,
          Nat.pow_succ, Nat.pow_succ]
      ring_nat

/-- ★★ **`C(2m+1, m) ≤ 4^m`** — the odd central binomial bound, ∅-axiom. -/
theorem odd_central_binom_le (m : Nat) : choose (2 * m + 1) m ≤ 4 ^ m := by
  have hsym : choose (2 * m + 1) m = choose (2 * m + 1) (m + 1) := by
    rw [show 2 * m + 1 = m + (m + 1) from by ring_nat]; exact choose_symm m (m + 1)
  have hrow : sumTo (2 * m + 1 + 1) (fun k => choose (2 * m + 1) k) = 2 ^ (2 * m + 1) :=
    pascal_row_sum (2 * m + 1)
  have hjn : m + 1 < 2 * m + 1 + 1 := by
    rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) from by ring_nat]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos m)
  have htwo : (fun k => choose (2 * m + 1) k) m + (fun k => choose (2 * m + 1) k) (m + 1)
      ≤ sumTo (2 * m + 1 + 1) (fun k => choose (2 * m + 1) k) :=
    two_terms_le_sumTo (fun k => choose (2 * m + 1) k) (Nat.lt_succ_self m) hjn
  have heq : choose (2 * m + 1) m + choose (2 * m + 1) (m + 1) = 2 * choose (2 * m + 1) m := by
    rw [← hsym]; ring_nat
  have h2c : 2 * choose (2 * m + 1) m ≤ 2 ^ (2 * m + 1) := by
    rw [← hrow, ← heq]; exact htwo
  have hpow : (2 : Nat) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [four_pow_eq, Nat.pow_succ]; ring_nat
  rw [hpow] at h2c
  exact Nat.le_of_mul_le_mul_left h2c (by decide)

end E213.Lib.Math.NumberTheory.OddCentralBinom
