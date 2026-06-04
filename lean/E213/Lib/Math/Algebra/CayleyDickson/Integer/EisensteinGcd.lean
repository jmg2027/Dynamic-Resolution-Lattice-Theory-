import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
import E213.Meta.Int213.OrderMul
import E213.Meta.Algebra213.Core

/-!
# EisensteinGcd — the Euclidean gcd + Bezout in `ℤ[ω]`

With `ℤ[ω]` norm-Euclidean (`EisensteinDivStep.zomega_div_step`), the gcd of two elements
exists, divides both, and is a `ℤ[ω]`-linear combination (Bezout) — proved by **fuel
induction** on `‖β‖².natAbs` using the Euclidean step `α = βγ + ρ` (`‖ρ‖² < ‖β‖²`).

  * `Dvd ZOmega` — `a ∣ b := ∃ c, b = a·c`.
  * `zdvd_add`, ★`zdvd_combo` — the Euclidean-step divisibility transfer.
  * `bezout_rearrange` — the 5-variable Bezout identity, by manual `Ring213` calc (the
    `cassini_ring` pattern; `ring_intZ` cannot see through ZOmega projections at this size).
  * ★★★★ `gcd_bezout` — `∀ n α β, ‖β‖².natAbs ≤ n → ∃ d s t, d = s·α + t·β ∧ d∣α ∧ d∣β`:
    the gcd exists, divides both, with explicit Bezout coefficients.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (zomega_div_step normSq_pos)
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

/-- Divisibility in `ℤ[ω]`: `a ∣ b` iff `b = a · c` for some `c`. -/
instance : Dvd ZOmega := ⟨fun a b => ∃ c, b = a * c⟩

/-- `d ∣ x → d ∣ y → d ∣ x + y`. -/
theorem zdvd_add {d x y : ZOmega} (hx : d ∣ x) (hy : d ∣ y) : d ∣ x + y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [ha, hb, ← mul_add]⟩

/-- ★★★ **The Euclidean-step divisibility transfer.** `d ∣ β → d ∣ ρ → α = βγ + ρ → d ∣ α`. -/
theorem zdvd_combo {d α β γ ρ : ZOmega} (hβ : d ∣ β) (hρ : d ∣ ρ)
    (hα : α = β * γ + ρ) : d ∣ α := by
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨c, hc⟩ := hρ
  exact ⟨b * γ + c, by rw [hα, hb, hc, mul_assoc, ← mul_add]⟩

/-! ## §2 — `ofInt`-unit algebra (ZOmega has no Lean `One` instance) -/

theorem ofInt_one_mul (a : ZOmega) : ZOmega.ofInt 1 * a = a := by
  refine ZOmega.ext ?_ ?_
  · show (1 : Int) * a.re - 0 * a.im = a.re
    rw [zero_mul, sub_zero, one_mulZ]
  · show (1 : Int) * a.im + 0 * a.re - 0 * a.im = a.im
    rw [zero_mul, zero_mul, sub_zero, one_mulZ, int_add_comm, int_zero_add]

theorem mul_ofInt_one (a : ZOmega) : a * ZOmega.ofInt 1 = a := by
  refine ZOmega.ext ?_ ?_
  · show a.re * 1 - a.im * 0 = a.re
    rw [mul_zeroZ, sub_zero, mul_one]
  · show a.re * 0 + a.im * 1 - a.im * 0 = a.im
    rw [mul_zeroZ, mul_zeroZ, sub_zero, mul_one, int_zero_add]

/-- `a ∣ a` (witness `ofInt 1`). -/
theorem zdvd_refl (a : ZOmega) : a ∣ a := ⟨ZOmega.ofInt 1, (mul_ofInt_one a).symm⟩

/-- `a ∣ 0` (witness `ofInt 0`). -/
theorem zdvd_zero (a : ZOmega) : a ∣ (0 : ZOmega) := ⟨ZOmega.ofInt 0, (mul_zero a).symm⟩

/-! ## §3 — the Bezout rearrangement identity (manual `Ring213` calc) -/

/-- `A + B + (S + -A) = S + B` over any `Ring213`. -/
theorem rearrange_helper {α} [Ring213 α] (A B S : α) : A + B + (S + -A) = S + B := by
  rw [add_comm S (-A), add_4_swap_mid A B (-A) S, add_comm A (-A), neg_add_cancel_self,
      zero_add, add_comm B S]

/-- The Bezout rearrangement: `t·(βγ+ρ) + (s−tγ)·β = s·β + t·ρ`. -/
theorem bezout_rearrange (s t β ρ γ : ZOmega) :
    t * (β * γ + ρ) + (s - t * γ) * β = s * β + t * ρ := by
  show t * (β * γ + ρ) + (s + -(t * γ)) * β = s * β + t * ρ
  have h1 : (s + -(t * γ)) * β = s * β + -(t * (β * γ)) := by
    rw [add_mul, neg_mul, mul_assoc, E213.Meta.Algebra213.CommRing213.mul_comm γ β]
  rw [mul_add, h1]
  exact rearrange_helper (t * (β * γ)) (t * ρ) (s * β)

/-! ## §4 — `‖β‖².natAbs = 0 ⟹ β = 0`, and the fuel-induction gcd -/

theorem normSq_natAbs_zero {β : ZOmega} (h : β.normSq.natAbs = 0) : β = 0 := by
  have hz : β.normSq = 0 := by
    have hc := E213.Meta.Int213.OrderMul.natAbs_cast_of_nonneg (normSq_nonneg β)
    rw [h] at hc
    exact hc.symm
  exact (normSq_eq_zero_iff β).mp hz

/-- ★★★★ **The `ℤ[ω]` Euclidean gcd + Bezout.**  For any `α β` with `‖β‖².natAbs ≤ n`, there
    is a `d` dividing both, with explicit Bezout coefficients `d = s·α + t·β`.  Fuel induction
    on `n`: base `β = 0` gives `d = α`; the step uses the Euclidean division
    `α = βγ + ρ` (`zomega_div_step`), recurses on `(β, ρ)` (`‖ρ‖².natAbs < ‖β‖².natAbs`,
    `natAbs_lt_of_lt`), transfers divisibility by `zdvd_combo`, and rearranges Bezout by
    `bezout_rearrange`. -/
theorem gcd_bezout : ∀ (n : Nat) (α β : ZOmega), β.normSq.natAbs ≤ n →
    ∃ d s t : ZOmega, d = s * α + t * β ∧ (d ∣ α) ∧ (d ∣ β) := by
  intro n
  induction n with
  | zero =>
    intro α β hβ
    have hβ0 : β = 0 := normSq_natAbs_zero (Nat.le_zero.mp hβ)
    refine ⟨α, ZOmega.ofInt 1, ZOmega.ofInt 0, ?_, zdvd_refl α, by rw [hβ0]; exact zdvd_zero α⟩
    rw [hβ0, ofInt_one_mul, mul_zero, add_zero]
  | succ n ih =>
    intro α β hβ
    rcases Nat.eq_zero_or_pos β.normSq.natAbs with h0 | hpos
    · have hβ0 : β = 0 := normSq_natAbs_zero h0
      refine ⟨α, ZOmega.ofInt 1, ZOmega.ofInt 0, ?_, zdvd_refl α,
        by rw [hβ0]; exact zdvd_zero α⟩
      rw [hβ0, ofInt_one_mul, mul_zero, add_zero]
    · have hβne : β ≠ 0 := by
        intro h; rw [h] at hpos; exact absurd hpos (by decide)
      obtain ⟨γ, ρ, hα, hρ⟩ := zomega_div_step α β hβne
      have hfuel : ρ.normSq.natAbs ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (natAbs_lt_of_lt (normSq_nonneg ρ) hρ) hβ)
      obtain ⟨d, s, t, hd, hdβ, hdρ⟩ := ih β ρ hfuel
      have hdα : d ∣ α := zdvd_combo hdβ hdρ hα
      refine ⟨d, t, s - t * γ, ?_, hdα, hdβ⟩
      rw [hd, hα]
      exact (bezout_rearrange s t β ρ γ).symm

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
