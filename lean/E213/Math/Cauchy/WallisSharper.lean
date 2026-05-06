import E213.Math.Cauchy.WallisSeq

/-!
# WallisSharper: π/2 > 64/45 strict bound (n ≥ 2)

Sharper version of the W_n ≥ 4/3 bound from PAPER1 §7.5.

## Core

`wallis_sharper_lower`: `n ≥ 2 → 45 * wallisNum n ≥ 64 *
wallisDen n`.  W_2 = 64/45 base, then monotonic increase.

The inductive step uses `4(k+1)² ≥ (2k+1)(2k+3)` (degree-2
polynomial identity), closed via the Flat-Monomial Strategy.

## Significance

The `orderProj 64 45` cut closes for `m/k = 64/45`.
Additional threshold cuts in (4/3, 64/45) can also be added
case-by-case.
-/

namespace E213.Math.Cauchy.WallisSharper

open E213.Firmware E213.Lens
open E213.Math.Cauchy.WallisSeq

/-- Polynomial: `4(k+1)² ≥ (2k+1)(2k+3)`. -/
private theorem poly_ineq (k : Nat) :
    4 * (k + 1) * (k + 1) ≥ (2 * k + 1) * (2 * k + 3) := by
  have e1 : 4 * (k + 1) * (k + 1) = 4 + 8 * k + 4 * (k * k) := by
    have := Nat.mul_mul_mul_comm 4 (k+1) 1 (k+1)
    have ee : (4 * (k+1)) * (k+1) = 4 * ((k+1) * (k+1)) := by
      rw [Nat.mul_assoc]
    rw [ee]
    have step : (k+1) * (k+1) = k*k + 2*k + 1 := by
      have : (k+1)*(k+1) = k*(k+1) + 1*(k+1) := Nat.add_mul k 1 (k+1)
      rw [this, Nat.mul_add, Nat.mul_add]; omega
    rw [step]; omega
  have e2 : (2 * k + 1) * (2 * k + 3) = 3 + 8 * k + 4 * (k * k) := by
    have h0 : (2*k+1) * (2*k+3) = 2*k*(2*k+3) + 1*(2*k+3) := Nat.add_mul _ _ _
    have h1 : 2*k*(2*k+3) = 2*k*(2*k) + 2*k*3 := Nat.mul_add _ _ _
    have h2 : 1*(2*k+3) = 1*(2*k) + 1*3 := Nat.mul_add _ _ _
    have h3 : 2*k*(2*k) = 4 * (k*k) := Nat.mul_mul_mul_comm _ _ _ _
    rw [h0, h1, h2, h3]; omega
  rw [e1, e2]; omega

end E213.Math.Cauchy.WallisSharper

namespace E213.Math.Cauchy.WallisSharper

open E213.Firmware E213.Lens
open E213.Math.Cauchy.WallisSeq

/-- **W_n ≥ 64/45 strict** (n ≥ 2): 45 * wallisNum n ≥ 64 *
    wallisDen n.  Inductive base W_2 = 64/45, then monotonic
    via 4(k+1)² ≥ (2k+1)(2k+3). -/
theorem wallis_sharper_lower (n : Nat) (hn : n ≥ 2) :
    45 * wallisNum n ≥ 64 * wallisDen n := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 1
      · subst hk
        show 45 * wallisNum 2 ≥ 64 * wallisDen 2
        decide
      · have hk2 : k ≥ 2 := by omega
        have h_inv := ih hk2
        have h_poly := poly_ineq k
        show 45 * (wallisNum k * (4 * (k+1) * (k+1))) ≥
             64 * (wallisDen k * ((2*k+1) * (2*k+3)))
        -- IH * (4*(k+1)*(k+1)) and poly * (64 * wallisDen k)
        have h1 : 45 * wallisNum k * (4 * (k+1) * (k+1)) ≥
                  64 * wallisDen k * (4 * (k+1) * (k+1)) :=
          Nat.mul_le_mul_right _ h_inv
        have h2 : 64 * wallisDen k * (4 * (k+1) * (k+1)) ≥
                  64 * wallisDen k * ((2*k+1) * (2*k+3)) :=
          Nat.mul_le_mul_left (64 * wallisDen k) h_poly
        have eq1 : 45 * (wallisNum k * (4 * (k+1) * (k+1)))
                 = 45 * wallisNum k * (4 * (k+1) * (k+1)) :=
          (Nat.mul_assoc _ _ _).symm
        have eq2 : 64 * (wallisDen k * ((2*k+1) * (2*k+3)))
                 = 64 * wallisDen k * ((2*k+1) * (2*k+3)) :=
          (Nat.mul_assoc _ _ _).symm
        rw [eq1, eq2]
        exact Nat.le_trans h2 h1

end E213.Math.Cauchy.WallisSharper
