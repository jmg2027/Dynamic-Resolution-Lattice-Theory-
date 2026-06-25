import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Meta.Int213.OrderMul
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid

/-!
# A norm-`p` Eisenstein element is prime — Euclid's lemma in `ℤ[ω]` (rung 3c-core, ∅-axiom)

★★★★★ `norm_prime_euclid` : if `π ∈ ℤ[ω]` has prime norm `‖π‖² = p` and `π ∣ αβ`, then

  `π ∣ α  ∨  π ∣ β`.

So `π` is **prime** in `ℤ[ω]`, hence `ℤ[ω]/(π)` is an **integral domain** (`residue_no_zero_divisors`).
This is the missing structural fact behind reading the cubic character's value *exactly* into
`μ₃ = {1, ω, ω²}` (rung 3c): `χ(α)³ ≡ 1` factors as `(χ−1)(χ−ω)(χ−ω²) ≡ 0`, and primality forces one
factor to vanish.

## The proof — the Euclidean gcd dichotomy *is* a constructive case split

`gcd_bezout` (the `ℤ[ω]` Euclidean algorithm) produces a common divisor `d = s·α + t·π` of `α` and `π`.
Because `d ∣ π` and `‖π‖² = p` is prime, `‖d‖² ∈ {1, p}` (`normSq_dvd_dichotomy`):

  * `‖d‖² = p` — then `d` is an **associate** of `π` (`dvd_of_associate`, the cofactor has norm 1, a
    unit), so `π ∣ d ∣ α`: the **left** disjunct.
  * `‖d‖² = 1` — then `d` is a **unit**, so `1 = (s·α + t·π)·conj d`; multiplying by `β` and using
    `π ∣ αβ` gives `π ∣ β`: the **right** disjunct.

No excluded middle: the dichotomy on `‖d‖²` directly delivers the `∨`.  ∅-axiom throughout.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
  (normSq_dvd_of_dvd unit_of_normSq_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
  (gcd_bezout zdvd_add ofInt_one_mul mul_ofInt_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinResidue (zdvd_trans)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Meta.Algebra213.Ring213 (mul_assoc add_mul add_zero)
open E213.Meta.Int213.OrderMul (natAbs_cast_of_nonneg le_of_mul_le_mul_right_pos ofNat_le_of_le)
open E213.Meta.Int213.Order (le_antisymm lt_of_lt_of_le le_refl)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)

/-- **Prime-norm divisor dichotomy** — if `d ∣ (norm `p`) so `‖d‖² ∣ p` and `p` is prime, then
    `‖d‖² = 1` or `‖d‖² = p`.  Cast `‖d‖² ∣ p` to `‖d‖².natAbs ∣ p` in `ℕ`, apply primality, lift back
    via `‖d‖² ≥ 0`. -/
theorem normSq_dvd_dichotomy {d : ZOmega} {p : Nat}
    (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (hdp : d.normSq ∣ (p : Int)) :
    d.normSq = 1 ∨ d.normSq = (p : Int) := by
  have hk : d.normSq.natAbs ∣ p := by
    have hcast : (d.normSq.natAbs : Int) ∣ (p : Int) := by
      rw [natAbs_cast_of_nonneg (normSq_nonneg d)]; exact hdp
    have hh := int_dvd_to_nat d.normSq.natAbs (p : Int) hcast
    rwa [Int.natAbs_ofNat] at hh
  have hnn : (d.normSq.natAbs : Int) = d.normSq := natAbs_cast_of_nonneg (normSq_nonneg d)
  rcases hpr _ hk with h1 | hpp
  · left; rw [← hnn, h1]; decide
  · right; rw [← hnn, hpp]

/-- **A norm-equal divisor is an associate** — if `d ∣ π` with `‖π‖² = ‖d‖² > 0`, then `π ∣ d`.  The
    cofactor `e` (`π = d·e`) has `‖e‖² = 1` (cancel `‖d‖²`), so `e` is a unit and `d = π·conj e`. -/
theorem dvd_of_associate {d π : ZOmega} (hdπ : d ∣ π) (hnorm : π.normSq = d.normSq)
    (hpos : 0 < d.normSq) : π ∣ d := by
  obtain ⟨e, he⟩ := hdπ
  have hn : d.normSq * e.normSq = d.normSq := by rw [← normSq_mul, ← he]; exact hnorm
  have he1 : e.normSq = 1 := by
    have hle : e.normSq ≤ 1 := le_of_mul_le_mul_right_pos (c := d.normSq)
      (by rw [Int.one_mul, E213.Meta.Int213.mul_comm e.normSq d.normSq, hn]; exact le_refl _) hpos
    have hge : (1 : Int) ≤ e.normSq := le_of_mul_le_mul_right_pos (c := d.normSq)
      (by rw [Int.one_mul, E213.Meta.Int213.mul_comm e.normSq d.normSq, hn]; exact le_refl _) hpos
    exact le_antisymm hle hge
  have hd : π * e.conj = d := by
    rw [he, mul_assoc, unit_of_normSq_one e he1, mul_ofInt_one]
  exact ⟨e.conj, hd.symm⟩

/-- ★★★★★ **A norm-`p` Eisenstein element is prime** — `‖π‖² = p` prime, `π ∣ αβ` ⟹ `π ∣ α ∨ π ∣ β`.
    The Euclidean gcd `d = s·α + t·π` of `α, π` has `‖d‖² ∈ {1, p}`; `‖d‖² = p` makes `d` an associate
    of `π` (`π ∣ d ∣ α`), `‖d‖² = 1` makes `d` a unit (Bezout ⟹ `π ∣ β`).  ∅-axiom, no excluded
    middle. -/
theorem norm_prime_euclid {π α β : ZOmega} {p : Nat}
    (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (hp1 : 1 < p) (hπ : π.normSq = (p : Int))
    (hdvd : π ∣ α * β) : π ∣ α ∨ π ∣ β := by
  obtain ⟨d, s, t, hbez, hdα, hdπ⟩ := gcd_bezout π.normSq.natAbs α π (Nat.le_refl _)
  have hdnorm : d.normSq ∣ (p : Int) := by
    obtain ⟨c, hc⟩ := hdπ
    have h := normSq_dvd_of_dvd d π c hc
    rwa [hπ] at h
  rcases normSq_dvd_dichotomy hpr hdnorm with h1 | hpp
  · -- unit case: π ∣ β
    right
    have hunit : d * d.conj = ofInt 1 := unit_of_normSq_one d h1
    have hone : ofInt 1 = (s * α) * d.conj + (t * π) * d.conj := by
      rw [← hunit, hbez, add_mul]
    have hβ : (s * α) * d.conj * β + (t * π) * d.conj * β = β := by
      rw [← add_mul, ← hone, ofInt_one_mul]
    -- `π ∣ Y · X` whenever `π ∣ X`
    have dvd_mul_of : ∀ Y X : ZOmega, π ∣ X → π ∣ Y * X := by
      intro Y X hX
      obtain ⟨w, hw⟩ := hX
      exact ⟨Y * w, by rw [hw, ← mul_assoc, mul_comm Y π, mul_assoc]⟩
    -- term 1 carries the `α·β` factor
    have hterm1 : (s * α) * d.conj * β = (s * d.conj) * (α * β) := by
      rw [mul_assoc s α d.conj, mul_comm α d.conj, ← mul_assoc s d.conj α,
          mul_assoc (s * d.conj) α β]
    have hπ1 : π ∣ (s * α) * d.conj * β := by
      rw [hterm1]; exact dvd_mul_of (s * d.conj) (α * β) hdvd
    -- term 2 carries the `π` factor
    have hterm2 : (t * π) * d.conj * β = π * (t * d.conj * β) := by
      rw [mul_comm t π, mul_assoc π t d.conj, mul_assoc π (t * d.conj) β]
    have hπ2 : π ∣ (t * π) * d.conj * β := ⟨t * d.conj * β, hterm2⟩
    rw [← hβ]; exact zdvd_add hπ1 hπ2
  · -- associate case: π ∣ α
    left
    have hpos : 0 < d.normSq := by
      rw [hpp]
      have h1p : (1 : Int) ≤ (p : Int) := ofNat_le_of_le (Nat.le_of_lt hp1)
      exact lt_of_lt_of_le (show (0 : Int) < 1 by decide) h1p
    have hπd : π ∣ d := dvd_of_associate hdπ (hπ.trans hpp.symm) hpos
    exact zdvd_trans hπd hdα

/-- ★★★★ **`ℤ[ω]/(π)` is an integral domain** — for a norm-`p` (prime) `π`, `αβ ≡ 0 (mod π)` forces
    `α ≡ 0` or `β ≡ 0`.  The residue-congruence reading of `norm_prime_euclid` (`ModEq π x 0 = π ∣ x`,
    since `x + -0 = x`).  ∅-axiom. -/
theorem residue_no_zero_divisors {π α β : ZOmega} {p : Nat}
    (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (hp1 : 1 < p) (hπ : π.normSq = (p : Int))
    (hab : ModEq π (α * β) 0) :
    ModEq π α 0 ∨ ModEq π β 0 := by
  have hz0 : (-(0 : ZOmega)) = 0 := by decide
  have hdvd : π ∣ α * β := by
    have h : π ∣ (α * β + -0) := hab
    rwa [hz0, add_zero] at h
  rcases norm_prime_euclid hpr hp1 hπ hdvd with h | h
  · left;  show π ∣ (α + -0); rw [hz0, add_zero]; exact h
  · right; show π ∣ (β + -0); rw [hz0, add_zero]; exact h

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime
