import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianTwoSquare
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList

/-!
# ZSqrtNegSharp — the `D ≤ 2` bound on the `ℤ[√−D]` descent is sharp

`ZSqrtNegSplit.split_form` represents `p = a² + D·b²` for `p ∣ x²+D` only under `1 ≤ D ≤ 2`
(the covering radius² `(1+D)/4 < 1`).  This file proves that hypothesis is **necessary**, not an
artifact: the `D = 3` analog is outright false.

The witness is `p = 2`, `x = 1`: `2 ∣ 1² + 3 = 4`, yet `2 ≠ a² + 3b²` for all integers `a, b`
(a mod-`4` obstruction — `a² + 3b² ∈ {0,1,3} mod 4`, never `2`).  Structurally this is `ℤ[√−3]`
failing to be integrally closed (`ℤ[√−3] ⊊ ℤ[ω]`): `2` "splits" in the descent sense but is not a
norm of the non-maximal order.

  * `form_a2_3b2_mod4` — `a² + 3b² ≡ 0, 1`, or `3 (mod 4)`.
  * ★★★ `not_two_eq_a2_3b2` — `2 ≠ a² + 3b²`.
  * ★★★★ `descent_false_at_three` — the `D = 3` split conclusion fails on a hypothesis it should
    cover: the parametric `split_form` cannot extend past `D = 2`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSharp

open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianTwoSquare (sq4)
open E213.Lib.Math.NumberTheory.PolyRoot (dvd_add' not_dvd_of_natAbs_lt)

/-- `3b² ≡ 0` or `3 (mod 4)` (three times a square). -/
theorem three_sq_mod4 (b : Int) : (4 : Int) ∣ (3 * (b * b)) ∨ (4 : Int) ∣ (3 * (b * b) - 3) := by
  rcases sq4 b with hb | hb
  · left
    obtain ⟨c, hc⟩ := hb
    exact ⟨3 * c, by rw [hc]; ring_intZ⟩
  · right
    obtain ⟨c, hc⟩ := hb
    have hbb : b * b = 4 * c + 1 := by rw [← hc]; ring_intZ
    exact ⟨3 * c, by rw [hbb]; ring_intZ⟩

/-- `a² + 3b² ≡ 0, 1`, or `3 (mod 4)` — never `2`. -/
theorem form_a2_3b2_mod4 (a b : Int) :
    (4 : Int) ∣ (a * a + 3 * (b * b)) ∨ (4 : Int) ∣ (a * a + 3 * (b * b) - 1)
      ∨ (4 : Int) ∣ (a * a + 3 * (b * b) - 3) := by
  rcases sq4 a with ha | ha <;> rcases three_sq_mod4 b with hb | hb
  · left; exact dvd_add' ha hb
  · right; right
    have e : a * a + 3 * (b * b) - 3 = a * a + (3 * (b * b) - 3) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · right; left
    have e : a * a + 3 * (b * b) - 1 = (a * a - 1) + 3 * (b * b) := by ring_intZ
    rw [e]; exact dvd_add' ha hb
  · left
    have hsub : (4 : Int) ∣ ((a * a - 1) + (3 * (b * b) - 3)) := dvd_add' ha hb
    have e : a * a + 3 * (b * b) = ((a * a - 1) + (3 * (b * b) - 3)) + 4 := by ring_intZ
    rw [e]; exact dvd_add' hsub ⟨1, by ring_intZ⟩

/-- ★★★ **`2` is not of the form `a² + 3b²`.**  (The mod-`4` obstruction: `2 ∉ {0,1,3} mod 4`.) -/
theorem not_two_eq_a2_3b2 : ¬ ∃ a b : Int, (2 : Int) = a * a + 3 * (b * b) := by
  rintro ⟨a, b, h⟩
  rcases form_a2_3b2_mod4 a b with hd | hd | hd <;> rw [← h] at hd
  · exact not_dvd_of_natAbs_lt 4 (by decide) (by decide) hd
  · exact not_dvd_of_natAbs_lt 4 (by decide) (by decide) hd
  · exact not_dvd_of_natAbs_lt 4 (by decide) (by decide) hd

/-- ★★★★ **The `D = 3` split fails.**  No universal `p ∣ x²+3 ⟹ p = a²+3b²` can hold: `p = 2`,
    `x = 1` satisfies `2 ∣ 1²+3` but `2 ≠ a²+3b²`.  So `ZSqrtNegSplit.split_form`'s `D ≤ 2`
    hypothesis is sharp — the `ℤ[√−D]` cyclotomic descent stops exactly at the covering-radius
    bound, where `ℤ[√−3]` ceases to be the integrally-closed order. -/
theorem descent_false_at_three :
    ¬ (∀ (p : Nat) (x : Int), (p : Int) ∣ (x * x + 3) → ∃ a b : Int, (p : Int) = a * a + 3 * (b * b)) := by
  intro hsplit
  have hdvd : (2 : Int) ∣ (1 * 1 + 3) := ⟨2, by decide⟩
  obtain ⟨a, b, hab⟩ := hsplit 2 1 hdvd
  exact not_two_eq_a2_3b2 ⟨a, b, hab⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSharp
