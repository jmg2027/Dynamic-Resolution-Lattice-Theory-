import E213.Lib.Math.NumberTheory.AperyRecurrence

/-!
# Zeta3Numerator — the cleared harmonic part of the numerator recurrence

The numerator Apéry number `A(n) = H₃(n)·B(n) + K(n)` satisfies Apéry's recurrence
iff the kernel `K` satisfies an inhomogeneous one; the `H₃` (harmonic) part follows
from `apery_recurrence` plus the harmonic telescoping `H₃(n)−H₃(n−1)=1/n³`.

This file lands that harmonic part, ∅-axiom, in cleared form: with `ℓ` a common
multiple of the cubes `1³…N³` (later `ℓ=lcm(1..N)³`), `HL ℓ n = Σ_{i=1}^n ℓ/i³`
is the cleared `ℓ·H₃(n)`, and the cleared identity holds.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Zeta3Numerator

open E213.Lib.Math.NumberTheory.AperyRecurrence (B aperyLead apery_recurrence)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Meta.Nat.NatDiv213 (div_add_mod_pure mul_witness_iff_mod_eq_zero)

/-- `a ∣ b → a·(b/a) = b`, ∅-axiom. -/
private theorem dvd_mul_div {a b : Nat} (h : a ∣ b) : a * (b / a) = b := by
  rcases h with ⟨c, hc⟩
  have hmod : b % a = 0 := (mul_witness_iff_mod_eq_zero a b).mp ⟨c, hc.symm⟩
  have hdm := div_add_mod_pure b a
  rw [hmod, Nat.add_zero] at hdm
  exact hdm

/-- The cleared harmonic sum `HL ℓ n = Σ_{i=1}^n ℓ/i³` (`= ℓ·H₃(n)` when `i³ ∣ ℓ`). -/
def HL (ℓ : Nat) (n : Nat) : Nat := sumTo n (fun i => ℓ / ((i + 1) * (i + 1) * (i + 1)))

/-- The harmonic telescoping: `(n+1)³·HL ℓ (n+1) = (n+1)³·HL ℓ n + ℓ` when `(n+1)³ ∣ ℓ`. -/
theorem HL_step {ℓ n : Nat} (h : (n + 1) * (n + 1) * (n + 1) ∣ ℓ) :
    (n + 1) * (n + 1) * (n + 1) * HL ℓ (n + 1)
      = (n + 1) * (n + 1) * (n + 1) * HL ℓ n + ℓ := by
  show (n + 1) * (n + 1) * (n + 1) * sumTo (n + 1) (fun i => ℓ / ((i + 1) * (i + 1) * (i + 1)))
    = (n + 1) * (n + 1) * (n + 1) * sumTo n (fun i => ℓ / ((i + 1) * (i + 1) * (i + 1))) + ℓ
  rw [sumTo_succ, Nat.mul_add, dvd_mul_div h]

/-- ★★ **The cleared `H₃`-part of the numerator recurrence** (additive ℕ form):
    follows from `apery_recurrence` × `HL ℓ (j+1)` with the harmonic telescoping
    absorbing the `ℓ·B` terms.  (`ℓ` a common multiple of `(j+1)³`, `(j+2)³`.) -/
theorem harmonic_part_recurrence (j ℓ : Nat)
    (h1 : (j + 1) * (j + 1) * (j + 1) ∣ ℓ) (h2 : (j + 2) * (j + 2) * (j + 2) ∣ ℓ) :
    (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2) * B (j + 2)
      + ((j + 1) * (j + 1) * (j + 1) * HL ℓ j * B j + ℓ * B j)
    = aperyLead j * (HL ℓ (j + 1) * B (j + 1)) + ℓ * B (j + 2) := by
  have hs2 : (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2)
      = (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 1) + ℓ := HL_step h2
  have hs1 : (j + 1) * (j + 1) * (j + 1) * HL ℓ (j + 1)
      = (j + 1) * (j + 1) * (j + 1) * HL ℓ j + ℓ := HL_step h1
  have hrec := apery_recurrence j
  calc (j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2) * B (j + 2)
          + ((j + 1) * (j + 1) * (j + 1) * HL ℓ j * B j + ℓ * B j)
      = ((j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 2)) * B (j + 2)
          + ((j + 1) * (j + 1) * (j + 1) * HL ℓ j + ℓ) * B j := by ring_nat
    _ = ((j + 2) * (j + 2) * (j + 2) * HL ℓ (j + 1) + ℓ) * B (j + 2)
          + ((j + 1) * (j + 1) * (j + 1) * HL ℓ (j + 1)) * B j := by rw [hs2, hs1]
    _ = HL ℓ (j + 1) * ((j + 2) * (j + 2) * (j + 2) * B (j + 2)
          + (j + 1) * (j + 1) * (j + 1) * B j) + ℓ * B (j + 2) := by ring_nat
    _ = HL ℓ (j + 1) * (aperyLead j * B (j + 1)) + ℓ * B (j + 2) := by rw [hrec]
    _ = aperyLead j * (HL ℓ (j + 1) * B (j + 1)) + ℓ * B (j + 2) := by ring_nat

end E213.Lib.Math.NumberTheory.Zeta3Numerator
