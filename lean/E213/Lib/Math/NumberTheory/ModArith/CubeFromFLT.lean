import E213.Lib.Math.NumberTheory.ModArith.EisensteinCubeRoot
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# CubeFromFLT — from a non-cube-fixed element to the cube root (Phase 3 FLT connection)

Given a prime `p` with `p − 1 = 3m` (`m ≥ 1`), FLT (`a^(p−1) ≡ 1`), and a *non-fixed* element
(`a^m ≢ 1 mod p`), the value `z = a^m − 1` satisfies `p ∤ z` and `p ∣ z(z²+3z+3) = (a^m)³ − 1
= a^(p−1) − 1`, so `cube_root_of_order3` yields `x` with `p ∣ x²+x+1`.

  * ★★★ `cube_from_nonfixed` — assembles the above.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT

open E213.Lib.Math.NumberTheory.ModArith.EisensteinCubeRoot (cube_root_of_order3)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.NatHelper (sub_add_cancel add_sub_cancel_right add_mul_mod_self_pure mul_assoc)

/-- `1 ≤ a` ⟹ `1 ≤ aᵐ` (pure Nat induction). -/
theorem one_le_pow' (a : Nat) (ha : 1 ≤ a) : ∀ m, 1 ≤ a ^ m
  | 0 => by rw [Nat.pow_zero]; exact Nat.le_refl 1
  | m + 1 => by
    have h := Nat.mul_le_mul (one_le_pow' a ha m) ha
    rw [Nat.one_mul] at h
    rw [Nat.pow_succ]; exact h

/-- `a^(m+n) = aᵐ·aⁿ` — pure replacement for `Nat.pow_add` (which leaks `propext`). -/
theorem pow_add_pure (a m : Nat) : ∀ n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
      rw [Nat.add_succ, Nat.pow_succ, pow_add_pure a m n, Nat.pow_succ, mul_assoc]

/-- `a^(3m) = aᵐ·aᵐ·aᵐ` (pure, via `pow_add_pure`). -/
theorem pow_three_mul (a m : Nat) : a ^ (3 * m) = a ^ m * a ^ m * a ^ m := by
  have h3 : 3 * m = m + m + m := by ring_nat
  rw [h3, pow_add_pure, pow_add_pure]

/-- The cube identity `(z+1)³ = z(z²+3z+3) + 1` (subtraction-free, so `ring_nat` is clean). -/
theorem cube_identity (z : Nat) :
    (z + 1) * (z + 1) * (z + 1) = z * (z * z + 3 * z + 3) + 1 := by ring_nat

/-- `x % p = 1`, `1 < p` ⟹ `p ∣ x − 1`. -/
theorem dvd_sub_one_of_mod_one (p x : Nat) (h : x % p = 1) : p ∣ x - 1 := by
  have hdm : p * (x / p) + x % p = x := div_add_mod x p
  rw [h] at hdm
  -- p*(x/p) + 1 = x ⟹ x - 1 = p*(x/p)
  rw [← hdm, add_sub_cancel_right]
  exact ⟨x / p, rfl⟩

/-- `p ∣ x − 1`, `1 ≤ x`, `1 < p` ⟹ `x % p = 1`. -/
theorem mod_one_of_dvd_sub_one (p x : Nat) (hp : 1 < p) (hx : 1 ≤ x) (h : p ∣ x - 1) :
    x % p = 1 := by
  obtain ⟨j, hj⟩ := h
  have hxj : x = p * j + 1 := by
    have h1 := sub_add_cancel hx
    rw [hj] at h1
    exact h1.symm
  rw [hxj, Nat.mul_comm p j, Nat.add_comm (j * p) 1, add_mul_mod_self_pure 1 p j,
      Nat.mod_eq_of_lt hp]

/-- ★★★ **From a non-fixed element to the cube root.**  `p` prime, `p − 1 = 3m`, `m ≥ 1`,
    `a ≥ 1`, `a^(p−1) ≡ 1`, `a^m ≢ 1` ⟹ `∃ x, p ∣ x²+x+1`. -/
theorem cube_from_nonfixed (p a m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha : 1 ≤ a) (hm : 3 * m = p - 1)
    (hflt : a ^ (p - 1) % p = 1) (hnf : a ^ m % p ≠ 1) :
    ∃ x : Nat, p ∣ (x * x + x + 1) := by
  have ham1 : 1 ≤ a ^ m := one_le_pow' a ha m
  have hz1 : (a ^ m - 1) + 1 = a ^ m := sub_add_cancel ham1
  -- a^(p-1) = a^m * a^m * a^m
  have hpow : a ^ (p - 1) = a ^ m * a ^ m * a ^ m := by
    rw [← hm]; exact pow_three_mul a m
  -- cube identity
  have hcube : a ^ m * a ^ m * a ^ m
      = (a ^ m - 1) * ((a ^ m - 1) * (a ^ m - 1) + 3 * (a ^ m - 1) + 3) + 1 := by
    rw [← hz1]; exact cube_identity (a ^ m - 1)
  -- p ∣ a^(p-1) - 1 = z(z²+3z+3)
  have hdvd1 : p ∣ a ^ (p - 1) - 1 := dvd_sub_one_of_mod_one p (a ^ (p - 1)) hflt
  have heq : a ^ (p - 1) - 1
      = (a ^ m - 1) * ((a ^ m - 1) * (a ^ m - 1) + 3 * (a ^ m - 1) + 3) := by
    rw [hpow, hcube]
    exact add_sub_cancel_right _ 1
  have hdvd2 : p ∣ (a ^ m - 1) * ((a ^ m - 1) * (a ^ m - 1) + 3 * (a ^ m - 1) + 3) :=
    heq ▸ hdvd1
  -- p ∤ z
  have hpz : ¬ p ∣ (a ^ m - 1) := by
    intro hd
    exact hnf (mod_one_of_dvd_sub_one p (a ^ m) hp ham1 hd)
  exact cube_root_of_order3 p (a ^ m - 1) hp hpr hdvd2 hpz

end E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
