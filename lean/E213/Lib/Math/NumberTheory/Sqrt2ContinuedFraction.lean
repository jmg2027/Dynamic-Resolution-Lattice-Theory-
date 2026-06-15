import E213.Lib.Math.NumberTheory.PellNumbers
import E213.Meta.Int213.PolyIntMTactic

/-!
# The √2 continued-fraction convergents are the Pell solutions (∅-axiom)

The continued fraction of √2 is `[1; 2,2,2,…]` (all partial quotients 2 after the
first); its convergents are `1, 3/2, 7/5, 17/12, 41/29, …`.  This file proves the
convergent sequences (defined by the all-2s recurrence `x(n+2)=2x(n+1)+x n`) **are
exactly the Pell numbers**, bridging the CF and Pell clusters:

  * ★ `q_eq_P` : the denominators `qₙ = P(n+1)` (the Pell numbers).
  * ★ `p_eq_H` : the numerators `pₙ = H(n+1)` (the half-companion Pell numbers).
  * ★★ `cf_norm` : `pₙ² − 2qₙ² = (−1)^{n+1}` — the convergents `pₙ/qₙ` solve the
    Pell equation `x²−2y²=±1` (the convergents of √2 ARE the Pell-equation
    solutions).  A corollary of `PellNumbers.norm` via the identifications.

Genuinely absent (the corpus Pell-CF files are FSM/matrix; `PellNumbers` had no CF
connection).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Sqrt2ContinuedFraction

open E213.Lib.Math.NumberTheory.PellNumbers (P H P_rec H_rec norm)
open E213.Meta.Int213.PolyIntM (powInt)

/-- √2-CF convergent **denominators**: `q 0 = 1, q 1 = 2, q(n+2)=2q(n+1)+q n`. -/
def q : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) + q n

/-- √2-CF convergent **numerators**: `p 0 = 1, p 1 = 3, p(n+2)=2p(n+1)+p n`. -/
def p : Nat → Nat
  | 0 => 1
  | 1 => 3
  | n + 2 => 2 * p (n + 1) + p n

theorem q_rec (n : Nat) : q (n + 2) = 2 * q (n + 1) + q n := rfl
theorem p_rec (n : Nat) : p (n + 2) = 2 * p (n + 1) + p n := rfl

/-- Convergents `p/q = 1, 3/2, 7/5, 17/12, 41/29`. -/
theorem q_vals : q 0 = 1 ∧ q 1 = 2 ∧ q 2 = 5 ∧ q 3 = 12 ∧ q 4 = 29 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem p_vals : p 0 = 1 ∧ p 1 = 3 ∧ p 2 = 7 ∧ p 3 = 17 ∧ p 4 = 41 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Paired two-step: `q n = P (n+1)` AND `q (n+1) = P (n+2)`. -/
theorem q_eq_P_pair : ∀ n : Nat, q n = P (n + 1) ∧ q (n + 1) = P (n + 1 + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show q 0 = P 1
      rw [show q 0 = 1 from rfl, show P 1 = 1 from rfl]
    · show q 1 = P 2
      rw [show q 1 = 2 from rfl, show P 2 = 2 from rfl]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    show q (k + 1 + 1) = P (k + 1 + 1 + 1)
    rw [q_rec k, P_rec (k + 1), ih1, ih0]

/-- ★ **√2-CF denominators are Pell numbers**: `qₙ = P(n+1)`. -/
theorem q_eq_P (n : Nat) : q n = P (n + 1) := (q_eq_P_pair n).1

/-- Paired two-step: `p n = H (n+1)` AND `p (n+1) = H (n+2)`. -/
theorem p_eq_H_pair : ∀ n : Nat, p n = H (n + 1) ∧ p (n + 1) = H (n + 1 + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show p 0 = H 1
      rw [show p 0 = 1 from rfl, show H 1 = 1 from rfl]
    · show p 1 = H 2
      rw [show p 1 = 3 from rfl, show H 2 = 3 from rfl]
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    show p (k + 1 + 1) = H (k + 1 + 1 + 1)
    rw [p_rec k, H_rec (k + 1), ih1, ih0]

/-- ★ **√2-CF numerators are half-companion Pell numbers**: `pₙ = H(n+1)`. -/
theorem p_eq_H (n : Nat) : p n = H (n + 1) := (p_eq_H_pair n).1

/-- ★★ **√2-CF convergents satisfy the Pell norm**: `pₙ² − 2·qₙ² = (−1)^{n+1}` —
    the convergents `pₙ/qₙ` solve `x²−2y²=±1` (the convergents of √2 ARE the
    Pell-equation solutions).  Corollary of `PellNumbers.norm (n+1)`. -/
theorem cf_norm (n : Nat) :
    (p n : Int) * (p n : Int) - 2 * ((q n : Int) * (q n : Int)) = powInt (-1) (n + 1) := by
  rw [p_eq_H n, q_eq_P n]
  exact norm (n + 1)

/-- Smoke: `p₀²−2q₀² = −1`, `p₁²−2q₁² = 1`, `p₃²−2q₃² = 1`. -/
theorem cf_norm_smoke :
    ((p 0 : Int) * p 0 - 2 * (q 0 * q 0) = -1)
    ∧ ((p 1 : Int) * p 1 - 2 * (q 1 * q 1) = 1)
    ∧ ((p 3 : Int) * p 3 - 2 * (q 3 * q 3) = 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberTheory.Sqrt2ContinuedFraction
