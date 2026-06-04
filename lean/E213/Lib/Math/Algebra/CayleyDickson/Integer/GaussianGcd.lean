import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep
import E213.Meta.Int213.OrderMul
import E213.Meta.Algebra213.Core

/-!
# GaussianGcd — the Euclidean gcd + Bezout in `ℤ[i]` (Gaussian Phase 2)

Disc-`−4` analog of `EisensteinGcd`: with `ℤ[i]` norm-Euclidean (`GaussianDivStep.zi_div_step`),
the gcd of two elements exists, divides both, and is a `ℤ[i]`-linear combination — by **fuel
induction** on `‖β‖².natAbs`.

  * `Dvd ZI`, `zdvd_add`, ★`zdvd_combo` — divisibility closure + the Euclidean-step transfer.
  * `bezout_rearrange` — the Bezout identity (generic `Ring213` calc).
  * ★★★★ `gcd_bezout` — `∀ n α β, ‖β‖².natAbs ≤ n → ∃ d s t, d = s·α + t·β ∧ d∣α ∧ d∣β`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianGcd

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep (zi_div_step normSq_pos)
open E213.Meta.Int213.OrderMul (natAbs_lt_of_lt)
open E213.Meta.Algebra213 (Ring213)
open E213.Meta.Algebra213.Ring213
  (add_mul mul_add mul_assoc add_comm neg_mul add_4_swap_mid neg_add_cancel_self
   zero_add add_zero mul_zero)
open E213.Meta.Algebra213.CommRing213 (mul_comm)
open E213.Meta.Int213 (zero_mul mul_one)
open E213.Meta.Int213 renaming zero_add → int_zero_add, add_comm → int_add_comm
open E213.Meta.Int213.Order (sub_zero)
open E213.Meta.Int213.PolyIntM (one_mulZ mul_zeroZ)

/-! ## §1 — `Dvd` and divisibility closure -/

/-- Divisibility in `ℤ[i]`: `a ∣ b` iff `b = a · c`. -/
instance : Dvd ZI := ⟨fun a b => ∃ c, b = a * c⟩

theorem zdvd_add {d x y : ZI} (hx : d ∣ x) (hy : d ∣ y) : d ∣ x + y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [ha, hb, ← mul_add]⟩

/-- ★★★ **The Euclidean-step divisibility transfer.** `d ∣ β → d ∣ ρ → α = βγ + ρ → d ∣ α`. -/
theorem zdvd_combo {d α β γ ρ : ZI} (hβ : d ∣ β) (hρ : d ∣ ρ) (hα : α = β * γ + ρ) : d ∣ α := by
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨c, hc⟩ := hρ
  exact ⟨b * γ + c, by rw [hα, hb, hc, mul_assoc, ← mul_add]⟩

/-! ## §2 — `ofInt`-unit algebra -/

theorem ofInt_one_mul (a : ZI) : ZI.ofInt 1 * a = a := by
  refine ZI.ext ?_ ?_
  · show (1 : Int) * a.re - 0 * a.im = a.re
    rw [zero_mul, sub_zero, one_mulZ]
  · show (1 : Int) * a.im + 0 * a.re = a.im
    rw [zero_mul, Int.add_zero, one_mulZ]

theorem mul_ofInt_one (a : ZI) : a * ZI.ofInt 1 = a := by
  refine ZI.ext ?_ ?_
  · show a.re * 1 - a.im * 0 = a.re
    rw [mul_zeroZ, sub_zero, mul_one]
  · show a.re * 0 + a.im * 1 = a.im
    rw [mul_zeroZ, int_zero_add, mul_one]

theorem zdvd_refl (a : ZI) : a ∣ a := ⟨ZI.ofInt 1, (mul_ofInt_one a).symm⟩

theorem zdvd_zero (a : ZI) : a ∣ (0 : ZI) := ⟨ZI.ofInt 0, (mul_zero a).symm⟩

/-! ## §3 — the Bezout rearrangement identity (generic `Ring213` calc) -/

theorem rearrange_helper {α} [Ring213 α] (A B S : α) : A + B + (S + -A) = S + B := by
  rw [add_comm S (-A), add_4_swap_mid A B (-A) S, add_comm A (-A), neg_add_cancel_self,
      E213.Meta.Algebra213.Ring213.zero_add, add_comm B S]

theorem bezout_rearrange (s t β ρ γ : ZI) :
    t * (β * γ + ρ) + (s - t * γ) * β = s * β + t * ρ := by
  show t * (β * γ + ρ) + (s + -(t * γ)) * β = s * β + t * ρ
  have h1 : (s + -(t * γ)) * β = s * β + -(t * (β * γ)) := by
    rw [add_mul, neg_mul, mul_assoc, E213.Meta.Algebra213.CommRing213.mul_comm γ β]
  rw [mul_add, h1]
  exact rearrange_helper (t * (β * γ)) (t * ρ) (s * β)

/-! ## §4 — the fuel-induction gcd -/

theorem normSq_natAbs_zero {β : ZI} (h : β.normSq.natAbs = 0) : β = 0 := by
  have hz : β.normSq = 0 := by
    have hc := E213.Meta.Int213.OrderMul.natAbs_cast_of_nonneg (normSq_nonneg β)
    rw [h] at hc
    exact hc.symm
  exact (normSq_eq_zero_iff β).mp hz

/-- ★★★★ **The `ℤ[i]` Euclidean gcd + Bezout.** -/
theorem gcd_bezout : ∀ (n : Nat) (α β : ZI), β.normSq.natAbs ≤ n →
    ∃ d s t : ZI, d = s * α + t * β ∧ (d ∣ α) ∧ (d ∣ β) := by
  intro n
  induction n with
  | zero =>
    intro α β hβ
    have hβ0 : β = 0 := normSq_natAbs_zero (Nat.le_zero.mp hβ)
    refine ⟨α, ZI.ofInt 1, ZI.ofInt 0, ?_, zdvd_refl α, by rw [hβ0]; exact zdvd_zero α⟩
    rw [hβ0, ofInt_one_mul, mul_zero, add_zero]
  | succ n ih =>
    intro α β hβ
    rcases Nat.eq_zero_or_pos β.normSq.natAbs with h0 | hpos
    · have hβ0 : β = 0 := normSq_natAbs_zero h0
      refine ⟨α, ZI.ofInt 1, ZI.ofInt 0, ?_, zdvd_refl α, by rw [hβ0]; exact zdvd_zero α⟩
      rw [hβ0, ofInt_one_mul, mul_zero, add_zero]
    · have hβne : β ≠ 0 := by
        intro h; rw [h] at hpos; exact absurd hpos (by decide)
      obtain ⟨γ, ρ, hα, hρ⟩ := zi_div_step α β hβne
      have hfuel : ρ.normSq.natAbs ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (natAbs_lt_of_lt (normSq_nonneg ρ) hρ) hβ)
      obtain ⟨d, s, t, hd, hdβ, hdρ⟩ := ih β ρ hfuel
      have hdα : d ∣ α := zdvd_combo hdβ hdρ hα
      refine ⟨d, t, s - t * γ, ?_, hdα, hdβ⟩
      rw [hd, hα]
      exact (bezout_rearrange s t β ρ γ).symm

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianGcd
