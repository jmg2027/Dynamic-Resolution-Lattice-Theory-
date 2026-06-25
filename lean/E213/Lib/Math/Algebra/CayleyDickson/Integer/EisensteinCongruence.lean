import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd

/-!
# Congruence in `ℤ[ω]` — `α ≡ β (mod π)` (∅-axiom)

★★★ `ModEq π α β := π ∣ (α − β)` — the congruence relation modulo an Eisenstein integer `π`, the
substrate for the **cubic-residue character** `(·/π)₃` (the character is a function of the residue
class of `α` mod `π`).  This file proves it is an **equivalence relation compatible with `+` and `·`**
— a congruence on the ring `ℤ[ω]` — exactly mirroring `Lens/Number/Nat213/Congruence` but on the
genuine ring (`ℤ[ω]` has real subtraction, so the difference form is direct, no symmetric workaround).

The quotient `ℤ[ω]/(π)` is then a ring; for `π` a prime of norm `p ≡ 1 (mod 3)` it is the field `𝔽_p`
(rung 2b), the home of the cubic character.  ∅-axiom throughout (the `Ring213` ring laws + the
Euclidean-`gcd` divisibility transfers `zdvd_add`/`zdvd_zero`).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd (zdvd_add zdvd_zero)
open E213.Meta.Algebra213 (Ring213)
open E213.Meta.Algebra213.Ring213
  (add_assoc add_comm add_zero add_left_neg mul_assoc add_mul neg_add neg_neg neg_mul
   zero_add add_4_swap_mid mul_neg)

/-- `a + -a = 0` (from `add_left_neg` + `add_comm`). -/
private theorem add_neg_self (a : ZOmega) : a + -a = 0 := by
  rw [add_comm]; exact add_left_neg a

/-- `π ∣ x → π ∣ -x`. -/
private theorem dvd_neg {d x : ZOmega} (h : d ∣ x) : d ∣ -x := by
  obtain ⟨c, rfl⟩ := h; exact ⟨-c, (mul_neg d c).symm⟩

/-- `π ∣ x → π ∣ x · e`. -/
private theorem dvd_mul_right {d x : ZOmega} (h : d ∣ x) (e : ZOmega) : d ∣ x * e := by
  obtain ⟨c, rfl⟩ := h; exact ⟨c * e, mul_assoc d c e⟩

/-- **Congruence modulo `π` in `ℤ[ω]`** — `α ≡ β (mod π)` iff `π` divides the difference `α − β`
    (written `α + -β`). -/
def ModEq (π α β : ZOmega) : Prop := π ∣ (α + -β)

/-- Reflexivity. -/
theorem refl (π α : ZOmega) : ModEq π α α := by
  show π ∣ (α + -α); rw [add_neg_self]; exact zdvd_zero π

/-- Symmetry — `β − α = −(α − β)`, and divisibility survives negation. -/
theorem symm {π α β : ZOmega} (h : ModEq π α β) : ModEq π β α := by
  show π ∣ (β + -α)
  have key : β + -α = -(α + -β) := by rw [neg_add, neg_neg, add_comm]
  rw [key]; exact dvd_neg h

/-- ★ Transitivity — `(α − β) + (β − γ) = α − γ`, then `zdvd_add`. -/
theorem trans {π α β γ : ZOmega} (h1 : ModEq π α β) (h2 : ModEq π β γ) : ModEq π α γ := by
  show π ∣ (α + -γ)
  have key : (α + -β) + (β + -γ) = α + -γ := by
    rw [add_assoc, ← add_assoc (-β) β (-γ), add_left_neg, zero_add]
  rw [← key]; exact zdvd_add h1 h2

/-- ★ Compatible with `+` — `α ≡ β`, `γ ≡ δ ⟹ α + γ ≡ β + δ`. -/
theorem add_compat {π α β γ δ : ZOmega} (h1 : ModEq π α β) (h2 : ModEq π γ δ) :
    ModEq π (α + γ) (β + δ) := by
  show π ∣ ((α + γ) + -(β + δ))
  have key : (α + γ) + -(β + δ) = (α + -β) + (γ + -δ) := by rw [neg_add, add_4_swap_mid]
  rw [key]; exact zdvd_add h1 h2

/-- ★ Compatible with right `·` — `α ≡ β ⟹ α · γ ≡ β · γ`. -/
theorem mul_right {π α β : ZOmega} (h : ModEq π α β) (γ : ZOmega) :
    ModEq π (α * γ) (β * γ) := by
  show π ∣ ((α * γ) + -(β * γ))
  have key : (α + -β) * γ = α * γ + -(β * γ) := by rw [add_mul, neg_mul]
  rw [← key]; exact dvd_mul_right h γ

/-- ★★★ **`ModEq π` is a congruence on `ℤ[ω]`** — an equivalence relation compatible with `+` and
    `·`.  The residue classes mod `π` form a ring `ℤ[ω]/(π)`; the cubic character lives on it. -/
theorem modEq_congruence (π : ZOmega) :
    (∀ a, ModEq π a a)
    ∧ (∀ a b, ModEq π a b → ModEq π b a)
    ∧ (∀ a b c, ModEq π a b → ModEq π b c → ModEq π a c)
    ∧ (∀ a b c d, ModEq π a b → ModEq π c d → ModEq π (a + c) (b + d))
    ∧ (∀ a b c, ModEq π a b → ModEq π (a * c) (b * c)) :=
  ⟨refl π, fun _ _ => symm, fun _ _ _ => trans, fun _ _ _ _ => add_compat,
   fun _ _ c h => mul_right h c⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
