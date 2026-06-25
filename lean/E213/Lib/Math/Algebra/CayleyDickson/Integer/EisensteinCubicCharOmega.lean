import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar
import E213.Meta.Nat.AddMod213

/-!
# The cubic character of the unit `ω` — `(ω/d)₃ = ω^m` (supplementary law, ∅-axiom)

★★★★ `char_omega_value` : the cubic character of the fundamental unit `ω` is a concrete cube root of
unity determined by `m mod 3` (`m = (p−1)/3`):

  `(ω/d)₃ = ω^m  ∈  {1, ω, ω²}`,

with `ω^m = ω^{m mod 3}` by the period-3 relation `ω³ = 1`.  This is the unit part of the
**supplementary laws** of cubic reciprocity (the character on `ω`, the analogue of the second
supplementary law of quadratic reciprocity).  Unlike a general element, `ω` is itself a unit of order
`3`, so `(ω/d)₃ = ω^m` needs **no** residue reduction — it is an exact identity in `ℤ[ω]`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (pow one pow_zero pow_succ one_mul omega_pow_three)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (pow_add)
open E213.Meta.Nat.AddMod213 (div_add_mod)

/-- ★★★ **`ω` has period 3 under powering** — `ω^{3k} = 1`.  Induction on `k` with `ω³ = 1`. -/
theorem pow_omega_three_mul : ∀ k : Nat, pow Omega (3 * k) = one
  | 0 => by rw [Nat.mul_zero]; rfl
  | k + 1 => by
      rw [Nat.mul_succ, pow_add, pow_omega_three_mul k, omega_pow_three, one_mul]

/-- The balanced residue cases of `m mod 3`. -/
private theorem mod_three_cases (m : Nat) : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by
  have h : m % 3 < 3 := Nat.mod_lt m (by decide)
  match m % 3, h with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr (Or.inl rfl)
  | 2, _ => exact Or.inr (Or.inr rfl)
  | n + 3, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 3 n))

/-- **Period-3 reduction** — `ω^i = ω^{i mod 3}`. -/
theorem pow_omega_mod (i : Nat) : pow Omega i = pow Omega (i % 3) := by
  have step : pow Omega (3 * (i / 3) + i % 3) = pow Omega (i % 3) := by
    rw [pow_add, pow_omega_three_mul, one_mul]
  rwa [div_add_mod] at step

/-- ★★★★ **The cubic character of `ω`.**  `(ω/d)₃ = ω^m` is one of the three cube roots of unity,
    determined by `m mod 3`: `ω^m = ω^{m mod 3} ∈ {1, ω, ω²}`.  The supplementary law for the unit
    `ω`.  `ω^m = ω^{m mod 3}` (period 3), then a three-way case on `m mod 3`.  ∅-axiom. -/
theorem char_omega_value (m : Nat) :
    pow Omega m = one ∨ pow Omega m = Omega ∨ pow Omega m = Omega * Omega := by
  have hkey : pow Omega m = pow Omega (m % 3) := pow_omega_mod m
  rcases mod_three_cases m with h0 | h1 | h2
  · left; rw [hkey, h0]; rfl
  · right; left; rw [hkey, h1]; show pow Omega 0 * Omega = Omega; rw [pow_zero, one_mul]
  · right; right; rw [hkey, h2]
    show (pow Omega 0 * Omega) * Omega = Omega * Omega
    rw [pow_zero, one_mul]

/-- ★★★★ **The cubic-character kernel is the cubic residues** — `ω^i = 1 ⟺ 3 ∣ i`.  The character
    `χ̂(i) = ωⁱ` is trivial exactly when the index is divisible by 3 (the element is a cubic residue).
    Period-3 reduction (`pow_omega_mod`) + `ω¹, ω² ≠ 1`.  ∅-axiom. -/
theorem pow_omega_one_iff (i : Nat) : pow Omega i = one ↔ 3 ∣ i := by
  constructor
  · intro h
    rw [pow_omega_mod] at h
    rcases mod_three_cases i with h0 | h1 | h2
    · exact ⟨i / 3, by have hd := div_add_mod i 3; rw [h0, Nat.add_zero] at hd; exact hd.symm⟩
    · rw [h1] at h; exact absurd h (by decide)
    · rw [h2] at h; exact absurd h (by decide)
  · intro ⟨k, hk⟩
    rw [hk]; exact pow_omega_three_mul k

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharOmega
