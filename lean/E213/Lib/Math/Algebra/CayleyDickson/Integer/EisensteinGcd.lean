import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
import E213.Meta.Algebra213.Core

/-!
# EisensteinGcd — divisibility closure in `ℤ[ω]` (toward the Euclidean gcd)

With `ℤ[ω]` norm-Euclidean (`EisensteinDivStep.zomega_div_step`), the split-prime descent's
gcd is built by fuel-induction on `‖·‖²` using the Euclidean step `α = βγ + ρ`.  The
divisibility reasoning at each step needs the closure lemmas this file provides (`Dvd ZOmega`
defined as `∃ c, b = a·c`):

  * `zdvd_add` — `d ∣ x → d ∣ y → d ∣ x + y`.
  * ★★★ `zdvd_combo` — `d ∣ β → d ∣ ρ → α = βγ + ρ → d ∣ α`: the Euclidean-step divisibility
    transfer (a common divisor of the divisor and remainder divides the dividend).

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Meta.Algebra213.Ring213 (mul_add mul_assoc)

/-- Divisibility in `ℤ[ω]`: `a ∣ b` iff `b = a · c` for some `c`. -/
instance : Dvd ZOmega := ⟨fun a b => ∃ c, b = a * c⟩

/-- `d ∣ x → d ∣ y → d ∣ x + y` (common factor of the summands). -/
theorem zdvd_add {d x y : ZOmega} (hx : d ∣ x) (hy : d ∣ y) : d ∣ x + y := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, by rw [ha, hb, ← mul_add]⟩

/-- ★★★ **The Euclidean-step divisibility transfer.**  If `d ∣ β` and `d ∣ ρ` and
    `α = βγ + ρ`, then `d ∣ α` — so a common divisor of the divisor `β` and remainder `ρ`
    divides the dividend `α`, the invariant carrying a gcd up the Euclidean recursion. -/
theorem zdvd_combo {d α β γ ρ : ZOmega} (hβ : d ∣ β) (hρ : d ∣ ρ)
    (hα : α = β * γ + ρ) : d ∣ α := by
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨c, hc⟩ := hρ
  exact ⟨b * γ + c, by rw [hα, hb, hc, mul_assoc, ← mul_add]⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
