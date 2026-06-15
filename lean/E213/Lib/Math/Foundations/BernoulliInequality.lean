import E213.Meta.Int213.Core
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Foundations.CauchySchwarzGeneral

/-!
# Bernoulli's inequality + QM–AM corollary of Cauchy–Schwarz (∅-axiom)

  * ★★★ `bernoulli` — `1 + n·x ≤ (1+x)^n` for `0 ≤ x` over `Int` (induction on `n`;
    the step multiplies the IH by `(1+x) ≥ 0` and drops the nonneg cross term `n·x²`).
  * ★★ `sq_sum_le` — `(Σ aᵢ)² ≤ n·(Σ aᵢ²)`, the `b ≡ 1` specialization of the general
    `cauchy_schwarz` (`Foundations/CauchySchwarzGeneral.lean`).

Note (`ring_intZ`): its normal form keeps zero-coefficient monomials, so `1 + 0·x = 1`
needs explicit `zero_mul`/`Int.add_zero`; and it needs beta-reduced goals (supply a
term lemma like `mul_one` inside `_congr` obligations).  All ∅-axiom.
-/

namespace E213.Lib.Math.Foundations.BernoulliInequality

open E213.Meta.Int213
open E213.Meta.Int213.Order
open E213.Meta.Int213.OrderMul
open E213.Lib.Math.Foundations.CauchySchwarzGeneral

/-! ## Bernoulli's inequality over `Int`, `x ≥ 0` -/

/-- `0 ≤ (n : Int)` for any `n : Nat`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Int) ≤ (n : Int) :=
  le_zero_of_nonneg ⟨n⟩

/-- The cross term `n·x² ≥ 0`. -/
theorem cross_nonneg (n : Nat) (x : Int) : (0 : Int) ≤ (n : Int) * (x * x) :=
  mul_nonneg (ofNat_nonneg n) (int_sq_nonneg x)

/-- ★★★ **Bernoulli's inequality** (Int, `x ≥ 0`): `1 + n·x ≤ (1 + x)^n`. -/
theorem bernoulli (x : Int) (hx : 0 ≤ x) (n : Nat) :
    1 + (n : Int) * x ≤ (1 + x)^n := by
  induction n with
  | zero =>
      show 1 + ((0 : Nat) : Int) * x ≤ (1 + x)^(0 : Nat)
      have he : (1 + x)^(0 : Nat) = 1 := rfl
      rw [he]
      show 1 + (0 : Int) * x ≤ 1
      have : 1 + (0 : Int) * x = 1 := by rw [zero_mul, Int.add_zero]
      rw [this]
      exact le_refl 1
  | succ m ih =>
      have h1x : (0 : Int) ≤ 1 + x := by
        have hh : (0 : Int) ≤ (1 : Int) := le_zero_of_nonneg ⟨1⟩
        exact add_nonneg hh hx
      have hmul : (1 + (m : Int) * x) * (1 + x) ≤ (1 + x)^m * (1 + x) :=
        mul_le_mul_right_nonneg ih (1 + x) h1x
      have hpow : (1 + x)^(m + 1) = (1 + x)^m * (1 + x) := rfl
      have hexp : (1 + (m : Int) * x) * (1 + x)
          = (1 + ((m : Nat) + 1 : Nat) * x) + (m : Int) * (x * x) := by
        show (1 + (m : Int) * x) * (1 + x)
          = (1 + ((m : Int) + 1) * x) + (m : Int) * (x * x)
        ring_intZ
      have hdrop : 1 + ((m : Nat) + 1 : Nat) * x ≤ (1 + (m : Int) * x) * (1 + x) := by
        rw [hexp]
        have hc := cross_nonneg m x
        have step : (1 + ((m : Int) + 1) * x) + 0
            ≤ (1 + ((m : Int) + 1) * x) + (m : Int) * (x * x) :=
          add_le_add_left hc (1 + ((m : Int) + 1) * x)
        have hz : (1 + ((m : Int) + 1) * x) + 0 = 1 + ((m : Int) + 1) * x := by ring_intZ
        rw [hz] at step
        exact step
      have hchain : 1 + ((m : Nat) + 1 : Nat) * x ≤ (1 + x)^(m + 1) := by
        rw [hpow]; exact le_trans hdrop hmul
      exact hchain

/-! ## QM–AM / Cauchy–Schwarz corollary (`b ≡ 1`) -/

/-- `dot a 1 n = Σ_{i<n} aᵢ`. -/
theorem dot_one (a : Nat → Int) (n : Nat) :
    dot a (fun _ => (1 : Int)) n = sumZ n a := by
  show sumZ n (fun i => a i * 1) = sumZ n a
  exact sumZ_congr n (fun i => a i * 1) a (fun i _ => mul_one (a i))

/-- `ssq 1 n = (n : Int)`. -/
theorem ssq_one (n : Nat) : ssq (fun _ => (1 : Int)) n = (n : Int) := by
  show sumZ n (fun _ => (1 : Int) * 1) = (n : Int)
  induction n with
  | zero => rfl
  | succ m ih =>
      show sumZ m (fun _ => (1 : Int) * 1) + (1 : Int) * 1 = ((m : Nat) + 1 : Nat)
      rw [ih]
      show (m : Int) + (1 : Int) * 1 = (m : Int) + 1
      ring_intZ

/-- ★★ **QM–AM corollary** of Cauchy–Schwarz: `(Σ aᵢ)² ≤ n · (Σ aᵢ²)`. -/
theorem sq_sum_le (a : Nat → Int) (n : Nat) :
    sumZ n a * sumZ n a ≤ (n : Int) * ssq a n := by
  have hcs := cauchy_schwarz a (fun _ => (1 : Int)) n
  rw [dot_one a n, ssq_one n] at hcs
  have hcomm : ssq a n * (n : Int) = (n : Int) * ssq a n := by
    generalize ssq a n = S
    ring_intZ
  rw [hcomm] at hcs
  exact hcs

end E213.Lib.Math.Foundations.BernoulliInequality
