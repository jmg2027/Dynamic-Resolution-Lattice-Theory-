import E213.Math.Cauchy.Archimedean

/-!
# Sqrt2Cut: Dedekind cut of √2 (213 irrational instance)

Mingu (b): "killer demo" — Dedekind cut of a genuine irrational
inside 213, without external ℝ.

## Strategy

Pell-like sequence: abLens.view (xs n) = (x_n, y_n) with
x_n² = 2 y_n² + 1.  x_n / y_n → √2 from above.

For (m, k) with 2k² < m² (m/k > √2 rationally): eventually
orderProj true (x*k ≤ y*m).

## Squared comparison key

x*k ≤ y*m ↔ (x*k)² ≤ (y*m)² (for positive Nat).
(x*k)² = x² * k² = (2y² + 1) * k² = 2y²k² + k².
(y*m)² = y² * m².
So x*k ≤ y*m iff 2y²k² + k² ≤ y²*m² iff k² ≤ y² * (m² - 2k²).
For m² > 2k²: (m² - 2k²) ≥ 1, so y² ≥ k² → conclusion.
-/

namespace E213.Math.Irrational.Sqrt2Cut

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Instances.AB E213.Math.Cauchy.Archimedean

/-- Pell-like condition. -/
def IsPellSol (x y : Nat) : Prop := x * x = 2 * y * y + 1

/-- Helper (forward): a ≤ b → a*a ≤ b*b. -/
private theorem nat_sq_le_of_le {a b : Nat} (h : a ≤ b) : a * a ≤ b * b :=
  Nat.mul_le_mul h h

/-- Helper (backward): a*a ≤ b*b → a ≤ b. -/
private theorem nat_le_of_sq_le {a b : Nat} (hsq : a * a ≤ b * b) : a ≤ b := by
  by_cases hba : b ≥ a
  · exact hba
  · exfalso
    have hab : a > b := Nat.lt_of_not_le hba
    have hapos : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le b) hab
    have h1 : b * a < a * a := Nat.mul_lt_mul_of_pos_right hab hapos
    have h2 : b * b ≤ b * a := Nat.mul_le_mul_left b (Nat.le_of_lt hab)
    exact absurd (Nat.lt_of_le_of_lt h2 h1) (Nat.not_lt_of_le hsq)

end E213.Math.Irrational.Sqrt2Cut

namespace E213.Math.Irrational.Sqrt2Cut

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Instances.AB E213.Math.Cauchy.Archimedean

/-- **Pell solutions: orderProj true when m/k > √2 (rationally
    captured as 2k² < m²)**.  Assumes y² ≥ k² (y sufficiently large). -/
theorem pell_orderProj_above (x y m k : Nat)
    (hPell : IsPellSol x y) (hmsq : 2 * k * k < m * m)
    (hy_large : k * k ≤ y * y) :
    orderProj m k (x, y) = true := by
  show decide (x * k ≤ y * m) = true
  apply decide_eq_true
  apply nat_le_of_sq_le
  -- Goal: (x * k) * (x * k) ≤ (y * m) * (y * m)
  have hPell' : x * x = 2 * (y * y) + 1 := by
    unfold IsPellSol at hPell
    have heq : 2 * y * y = 2 * (y * y) := E213.Tactic.Nat213.mul_assoc 2 y y
    rw [heq] at hPell; exact hPell
  have hxsq : x * k * (x * k) = (2 * (y * y) + 1) * (k * k) := by
    have e1 : x * k * (x * k) = (x * x) * (k * k) := by
      rw [E213.Tactic.Nat213.mul_assoc x k (x*k),
          ← E213.Tactic.Nat213.mul_assoc k x k, Nat.mul_comm k x,
          E213.Tactic.Nat213.mul_assoc, ← E213.Tactic.Nat213.mul_assoc]
    rw [e1, hPell']
  have hysq : y * m * (y * m) = (y * y) * (m * m) := by
    rw [E213.Tactic.Nat213.mul_assoc y m (y*m),
        ← E213.Tactic.Nat213.mul_assoc m y m, Nat.mul_comm m y,
        E213.Tactic.Nat213.mul_assoc, ← E213.Tactic.Nat213.mul_assoc]
  rw [hxsq, hysq]
  have hmm : 2 * (k * k) + 1 ≤ m * m := by
    have heq : 2 * k * k = 2 * (k * k) := E213.Tactic.Nat213.mul_assoc 2 k k
    rw [heq] at hmsq; exact hmsq
  have step1 : (y * y) * (2 * (k * k) + 1) ≤ (y * y) * (m * m) :=
    Nat.mul_le_mul_left (y * y) hmm
  have eA : (y * y) * (2 * (k * k) + 1) = 2 * (y * y) * (k * k) + y * y := by
    rw [Nat.mul_add, Nat.mul_one]
    congr 1
    rw [← E213.Tactic.Nat213.mul_assoc (y*y) 2, Nat.mul_comm (y*y) 2,
        E213.Tactic.Nat213.mul_assoc]
  have eB : (2 * (y * y) + 1) * (k * k) = 2 * (y * y) * (k * k) + k * k := by
    rw [E213.Tactic.Nat213.add_mul, Nat.one_mul]
  rw [eB]
  rw [eA] at step1
  -- step1 : 2*(y*y)*(k*k) + y*y ≤ (y*y)*(m*m)
  -- Goal: 2*(y*y)*(k*k) + k*k ≤ (y*y)*(m*m)
  -- Chain: k*k ≤ y*y → 2*(y*y)*(k*k) + k*k ≤ 2*(y*y)*(k*k) + y*y ≤ (y*y)*(m*m)
  exact Nat.le_trans (Nat.add_le_add_left hy_large _) step1

end E213.Math.Irrational.Sqrt2Cut

namespace E213.Math.Irrational.Sqrt2Cut

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Instances.AB E213.Math.Cauchy.Archimedean

/-- **Pell solutions: orderProj false when m/k < √2** (rationally
    captured as m² < 2k²).  Always (no y bound). -/
theorem pell_orderProj_below (x y m k : Nat)
    (hPell : IsPellSol x y) (hk : k ≥ 1) (hmsq : m * m < 2 * k * k) :
    orderProj m k (x, y) = false := by
  show decide (x * k ≤ y * m) = false
  apply decide_eq_false
  intro hle
  -- (x*k)² ≤ (y*m)² from hle
  have hle_sq : (x * k) * (x * k) ≤ (y * m) * (y * m) := nat_sq_le_of_le hle
  have hPell' : x * x = 2 * (y * y) + 1 := by
    unfold IsPellSol at hPell
    have heq : 2 * y * y = 2 * (y * y) := E213.Tactic.Nat213.mul_assoc 2 y y
    rw [heq] at hPell; exact hPell
  have hxsq : x * k * (x * k) = (2 * (y * y) + 1) * (k * k) := by
    have e1 : x * k * (x * k) = (x * x) * (k * k) := by
      rw [E213.Tactic.Nat213.mul_assoc x k (x*k),
          ← E213.Tactic.Nat213.mul_assoc k x k, Nat.mul_comm k x,
          E213.Tactic.Nat213.mul_assoc, ← E213.Tactic.Nat213.mul_assoc]
    rw [e1, hPell']
  have hysq : y * m * (y * m) = (y * y) * (m * m) := by
    rw [E213.Tactic.Nat213.mul_assoc y m (y*m),
        ← E213.Tactic.Nat213.mul_assoc m y m, Nat.mul_comm m y,
        E213.Tactic.Nat213.mul_assoc, ← E213.Tactic.Nat213.mul_assoc]
  rw [hxsq, hysq] at hle_sq
  -- hle_sq : (2*(y*y)+1) * (k*k) ≤ (y*y) * (m*m)
  have hmm_le : m * m + 1 ≤ 2 * (k * k) := by
    have heq : 2 * k * k = 2 * (k * k) := E213.Tactic.Nat213.mul_assoc 2 k k
    rw [heq] at hmsq; exact hmsq
  -- (y*y) * (m*m) ≤ (y*y) * (2*(k*k)) - (y*y) when y*y ≥ 1.
  -- Goal: derive False.  Strategy: show (2*(y*y)+1)*(k*k) > (y*y)*(m*m).
  --   (2*(y*y)+1)*(k*k) = 2*(y*y)*(k*k) + k*k
  --   (y*y)*(m*m) ≤ (y*y)*(2*(k*k)-1) when m*m ≤ 2*(k*k)-1.
  --   That's not pleasant in Nat.  Alternative: use hmm_le to bound.
  --   (y*y)*(m*m+1) ≤ (y*y)*(2*(k*k))
  --   (y*y)*(m*m) + (y*y) ≤ 2*(y*y)*(k*k)
  --   So (y*y)*(m*m) ≤ 2*(y*y)*(k*k) - (y*y) (Nat sub).
  --   Combined with hle_sq: 2*(y*y)*(k*k) + k*k ≤ 2*(y*y)*(k*k) - (y*y).
  --   Add (y*y) both sides: 2*(y*y)*(k*k) + k*k + y*y ≤ 2*(y*y)*(k*k).
  --   Cancel: k*k + y*y ≤ 0.  k*k ≥ 1 → contra.
  have hkk_pos : 1 ≤ k * k := Nat.mul_pos hk hk
  -- (y*y)*(m*m+1) ≤ (y*y)*(2*(k*k))
  have h_yMul : (y * y) * (m * m + 1) ≤ (y * y) * (2 * (k * k)) :=
    Nat.mul_le_mul_left (y * y) hmm_le
  have h_yMul_eq : (y * y) * (m * m + 1) = (y * y) * (m * m) + (y * y) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h_yMul_eq] at h_yMul
  -- h_yMul : (y*y)*(m*m) + (y*y) ≤ (y*y) * (2*(k*k))
  -- (y*y)*(2*(k*k)) = 2*(y*y)*(k*k)
  have h_2y_eq : (y * y) * (2 * (k * k)) = 2 * (y * y) * (k * k) := by
    rw [← E213.Tactic.Nat213.mul_assoc (y*y) 2, Nat.mul_comm (y*y) 2,
        E213.Tactic.Nat213.mul_assoc]
  rw [h_2y_eq] at h_yMul
  -- h_yMul : (y*y)*(m*m) + (y*y) ≤ 2*(y*y)*(k*k)
  -- hle_sq : (2*(y*y)+1) * (k*k) ≤ (y*y) * (m*m)
  -- (2*(y*y)+1)*(k*k) = 2*(y*y)*(k*k) + k*k
  have h_hle_eq : (2 * (y * y) + 1) * (k * k) = 2 * (y * y) * (k * k) + k * k := by
    rw [E213.Tactic.Nat213.add_mul, Nat.one_mul]
  rw [h_hle_eq] at hle_sq
  -- hle_sq : 2*(y*y)*(k*k) + k*k ≤ (y*y) * (m*m)
  -- Add (y*y) to both: 2*(y*y)*(k*k) + k*k + (y*y) ≤ (y*y)*(m*m) + (y*y) ≤ 2*(y*y)*(k*k)
  -- Cancel 2*(y*y)*(k*k): k*k + (y*y) ≤ 0.  k*k ≥ 1 → False.
  have h_chain : 2*(y*y)*(k*k) + k*k + (y*y) ≤ 2*(y*y)*(k*k) :=
    Nat.le_trans (Nat.add_le_add_right hle_sq (y*y)) h_yMul
  -- Add 0 to RHS: 2*(y*y)*(k*k) + k*k + (y*y) ≤ 2*(y*y)*(k*k) + 0
  have h_chain' : 2*(y*y)*(k*k) + (k*k + (y*y)) ≤ 2*(y*y)*(k*k) + 0 := by
    rw [Nat.add_zero, ← Nat.add_assoc]; exact h_chain
  -- Cancel: k*k + y*y ≤ 0
  have h_zero : k*k + (y*y) ≤ 0 :=
    E213.Tactic.Nat213.le_of_add_le_add_left h_chain'
  -- k*k ≥ 1 → k*k + y*y ≥ 1, contra h_zero.
  exact absurd (Nat.le_trans hkk_pos
    (Nat.le_trans (Nat.le_add_right (k*k) (y*y)) h_zero)) (by decide)

end E213.Math.Irrational.Sqrt2Cut
