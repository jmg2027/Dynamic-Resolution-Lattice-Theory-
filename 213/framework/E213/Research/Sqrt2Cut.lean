import E213.Research.ArchimedeanCauchy

/-!
# Research.Sqrt2Cut: √2 의 Dedekind cut (213 irrational instance)

Mingu (b): "killer demo" — 외부 ℝ 없이 213 안 에서 진짜 무리수
의 Dedekind cut.

## 전략

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

namespace E213.Research.Sqrt2Cut

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-- Pell-like 조건. -/
def IsPellSol (x y : Nat) : Prop := x * x = 2 * y * y + 1

/-- Helper: Nat squared comparison.  a ≤ b iff a*a ≤ b*b. -/
private theorem nat_le_iff_sq_le (a b : Nat) : a ≤ b ↔ a * a ≤ b * b := by
  constructor
  · intro h
    exact Nat.mul_le_mul h h
  · intro hsq
    by_cases hba : b ≥ a
    · exact hba
    · exfalso
      have hab : a > b := Nat.lt_of_not_le hba
      have hapos : 0 < a := by omega
      have h1 : b * a < a * a := Nat.mul_lt_mul_of_pos_right hab hapos
      have h2 : b * b ≤ b * a := Nat.mul_le_mul_left b (Nat.le_of_lt hab)
      have h3 : b * b < a * a := Nat.lt_of_le_of_lt h2 h1
      omega

end E213.Research.Sqrt2Cut

namespace E213.Research.Sqrt2Cut

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-- **Pell solutions: orderProj true when m/k > √2 (rationally
    captured as 2k² < m²)**.  y² ≥ k² 가정 (y 충분히 큰 경우). -/
theorem pell_orderProj_above (x y m k : Nat)
    (hPell : IsPellSol x y) (hmsq : 2 * k * k < m * m)
    (hy_large : k * k ≤ y * y) :
    orderProj m k (x, y) = true := by
  unfold orderProj
  show decide (x * k ≤ y * m) = true
  rw [decide_eq_true_iff]
  rw [nat_le_iff_sq_le]
  -- (x * k) * (x * k) = x * x * k * k = (2y² + 1) * k²
  -- (y * m) * (y * m) = y² * m²
  -- Goal after rw: x * k * (x * k) ≤ y * m * (y * m)
  -- = x*x*k*k vs y*y*m*m by Nat.mul comm/assoc
  -- x*x = 2*y*y + 1
  -- LHS = (2y²+1) * k², RHS = y² * m²
  -- LHS ≤ RHS iff k² ≤ y²(m² - 2k²)
  -- m² - 2k² ≥ 1, y² ≥ k² → y²(m² - 2k²) ≥ y² ≥ k². ✓
  have hPell' : x * x = 2 * (y * y) + 1 := by
    unfold IsPellSol at hPell
    have : 2 * y * y = 2 * (y * y) := by rw [Nat.mul_assoc]
    omega
  -- Define Q := y*y, K := k*k, M := m*m for omega
  have hxsq : x * k * (x * k) = (2 * (y * y) + 1) * (k * k) := by
    have e1 : x * k * (x * k) = (x * x) * (k * k) := by
      rw [Nat.mul_assoc, ← Nat.mul_assoc k x k, Nat.mul_comm k x,
          Nat.mul_assoc, ← Nat.mul_assoc]
    rw [e1, hPell']
  have hysq : y * m * (y * m) = (y * y) * (m * m) := by
    rw [Nat.mul_assoc, ← Nat.mul_assoc m y m, Nat.mul_comm m y,
        Nat.mul_assoc, ← Nat.mul_assoc]
  rw [hxsq, hysq]
  -- Goal: (2*(y*y) + 1) * (k*k) ≤ (y*y) * (m*m)
  -- Set Y := y*y, K := k*k, M := m*m.  hy_large: k*k ≤ y*y.  hmsq: 2*k*k < m*m.
  -- (2Y + 1) * K = 2YK + K.  Y * M ≥ Y * (2K + 1) = 2YK + Y.  Since Y ≥ K, 2YK + Y ≥ 2YK + K.
  have hmm : 2 * (k * k) + 1 ≤ m * m := by
    have : 2 * k * k = 2 * (k * k) := by rw [Nat.mul_assoc]
    omega
  have step1 : (y * y) * (2 * (k * k) + 1) ≤ (y * y) * (m * m) :=
    Nat.mul_le_mul_left (y * y) hmm
  -- (y*y) * (2*(k*k) + 1) = 2 * (y*y) * (k*k) + y*y
  -- (2*(y*y) + 1) * (k*k) = 2 * (y*y) * (k*k) + k*k
  -- Diff: y*y - k*k ≥ 0 (hy_large).
  have eA : (y * y) * (2 * (k * k) + 1) = 2 * (y * y) * (k * k) + y * y := by
    rw [Nat.mul_add, Nat.mul_one]
    congr 1
    rw [show 2 * (k * k) = 2 * (k * k) from rfl,
        ← Nat.mul_assoc (y*y) 2, Nat.mul_comm (y*y) 2, Nat.mul_assoc]
  have eB : (2 * (y * y) + 1) * (k * k) = 2 * (y * y) * (k * k) + k * k := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [eB]
  rw [eA] at step1
  omega

end E213.Research.Sqrt2Cut

namespace E213.Research.Sqrt2Cut

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens E213.Research.ArchimedeanCauchy

/-- **Pell solutions: orderProj false when m/k < √2** (rationally
    captured as m² < 2k²).  Always (no y bound). -/
theorem pell_orderProj_below (x y m k : Nat)
    (hPell : IsPellSol x y) (hk : k ≥ 1) (hmsq : m * m < 2 * k * k) :
    orderProj m k (x, y) = false := by
  unfold orderProj
  show decide (x * k ≤ y * m) = false
  rw [decide_eq_false_iff_not]
  -- Need: ¬ x * k ≤ y * m, i.e., y * m < x * k.
  -- (y*m)² ≤ (y*m+1) * (y*m + ...) — direct: show (y*m)² < (x*k)².
  -- (x*k)² = (2y² + 1) * k² = 2y²k² + k².
  -- (y*m)² = y² * m².
  -- Goal: y² * m² < 2y²k² + k².
  -- Since m² ≤ 2k² - 1 (since m² < 2k² strict, integer):
  --   y² * m² ≤ y² * (2k² - 1) = 2y²k² - y² ≤ 2y²k² - 0 = 2y²k².
  -- So y² * m² < 2y²k² + k² (since k² ≥ 1).
  intro hle
  rw [nat_le_iff_sq_le] at hle
  have hPell' : x * x = 2 * (y * y) + 1 := by
    unfold IsPellSol at hPell
    have : 2 * y * y = 2 * (y * y) := by rw [Nat.mul_assoc]
    omega
  have hxsq : x * k * (x * k) = (2 * (y * y) + 1) * (k * k) := by
    have e1 : x * k * (x * k) = (x * x) * (k * k) := by
      rw [Nat.mul_assoc, ← Nat.mul_assoc k x k, Nat.mul_comm k x,
          Nat.mul_assoc, ← Nat.mul_assoc]
    rw [e1, hPell']
  have hysq : y * m * (y * m) = (y * y) * (m * m) := by
    rw [Nat.mul_assoc, ← Nat.mul_assoc m y m, Nat.mul_comm m y,
        Nat.mul_assoc, ← Nat.mul_assoc]
  rw [hxsq, hysq] at hle
  -- hle: x * k * (x*k) ≤ y * m * (y*m), reformulated
  -- Goal: False. Use m² < 2k² and k ≥ 1.
  have hmm_le : m * m + 1 ≤ 2 * (k * k) := by
    have : 2 * k * k = 2 * (k * k) := by rw [Nat.mul_assoc]
    omega
  have hkk_pos : 1 ≤ k * k := by
    have : 0 < k := by omega
    exact Nat.mul_pos this this
  -- (y*y) * (m*m) < (2 * (y*y) + 1) * (k*k)
  -- Equivalent: (y*y) * (m*m + 1) ≤ (y*y) * (2*(k*k))
  -- And (y*y) * (2*(k*k)) + 1*(k*k) ≤ (2*(y*y) + 1) * (k*k) = 2*(y*y)*(k*k) + k*k
  have step1 : (y * y) * (m * m) < (y * y) * (2 * (k * k)) ∨ y * y = 0 := by
    rcases Nat.eq_zero_or_pos (y * y) with hy0 | hypos
    · right; exact hy0
    · left
      have := Nat.mul_le_mul_left (y * y) hmm_le
      have h2 : (y * y) * (m * m + 1) ≤ (y * y) * (2 * (k * k)) := this
      have h3 : (y * y) * (m * m + 1) = (y * y) * (m * m) + (y * y) := by
        rw [Nat.mul_add, Nat.mul_one]
      omega
  rcases step1 with hlt | hy0
  · -- (y*y)(m*m) < (y*y)(2*(k*k)) ≤ (2*(y*y) + 1)*(k*k) - 1 something...
    -- Actually: 2*(y*y)*(k*k) ≤ 2*(y*y)*(k*k) + k*k, but ≤ trivial.
    -- Goal: y² m² ≤ (2y²+1) k² = 2y²k² + k² ?
    -- We have y² m² < y² * 2k² = 2y² k².  So y² m² < 2y² k² ≤ 2y² k² + k² = (2y²+1) k².
    have hgoal : (y * y) * (m * m) < (2 * (y * y) + 1) * (k * k) := by
      have step2 : (y * y) * (2 * (k * k)) ≤ (2 * (y * y) + 1) * (k * k) := by
        have eA : (y * y) * (2 * (k * k)) = (2 * (y * y)) * (k * k) := by
          rw [← Nat.mul_assoc, Nat.mul_comm (y*y) 2, Nat.mul_assoc]
        rw [eA]
        have eB : (2 * (y * y) + 1) * (k * k)
                    = (2 * (y * y)) * (k * k) + k * k := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      omega
    omega
  · -- y = 0 case: y² m² = 0, (2y²+1) k² = k² ≥ 1.  0 ≤ k², strict 부재.
    -- hle becomes 0 ≤ 0, tautology, but we need strict inequality somewhere.
    -- Wait, hle was ≤ (not strict), and we need to find ¬ ≤ for False.
    -- Hmm.  Actually hle says x*k*(x*k) ≤ y*m*(y*m).  After rw to (2y²+1)k² ≤ y² m².
    -- If y = 0: LHS = (2*0 + 1) * k² = k² ≥ 1.  RHS = 0 * m² = 0.  k² ≤ 0 → k² = 0 → k = 0.
    -- But k ≥ 1, contradiction.
    have : (2 * (y * y) + 1) * (k * k) ≤ (y * y) * (m * m) := hle
    rw [hy0] at this
    simp at this
    omega

end E213.Research.Sqrt2Cut
