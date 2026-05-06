import E213.Math.Cauchy.PellSeq
import E213.Math.Cauchy.Archimedean
import E213.Math.Cauchy.MonotonicBounded

/-!
# EulerSeq: e (Euler) Dedekind cut via Σ 1/k!

Stirling-flavored partial sums for e:

- a_n = Σ_{k=0..n} n!/k!  (integer numerator with common denom n!)
- d_n = n!                (denominator)
- S_n = a_n / d_n  →  e ≈ 2.71828...

Pell-style demonstration: algebraic invariants `3 d_n ≥ a_n + 1`
(S_n < 3) and `a_n ≥ 2 d_n + 1` for n ≥ 2 (S_n > 2 from n=2).
Together: e ∈ (2, 3) Dedekind cut at concrete thresholds.

## Significance

PellSeq + Sqrt2Cut covers √2 (algebraic irrational); EulerSeq covers
e (transcendental).  A demonstration that the 213 framework can
accommodate even transcendentals via constructive Cauchy.

Status: ∅-axiom on every theorem (`tools/scan_axioms.py` reports
14 PURE / 0 DIRTY).
-/

namespace E213.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Math.Cauchy.Archimedean
open E213.Math.Cauchy.PellSeq

/-! ### Euler partial sum recursion -/

/-- Numerator a_n = Σ k=0..n n!/k!.
    Recursion: a_{n+1} = (n+1) * a_n + 1. -/
def eulerNum : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * eulerNum n + 1

/-- Denominator d_n = n!.  Recursion: d_{n+1} = (n+1) * d_n. -/
def eulerDen : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * eulerDen n

theorem eulerDen_pos (n : Nat) : 1 ≤ eulerDen n := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 1 ≤ (k + 1) * eulerDen k
      calc 1 = 1 * 1 := rfl
        _ ≤ (k + 1) * eulerDen k :=
            Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le k)) ih

theorem eulerNum_pos (_n : Nat) : 1 ≤ eulerNum _n := by
  induction _n with
  | zero => decide
  | succ k _ih =>
      show 1 ≤ (k + 1) * eulerNum k + 1
      exact Nat.le_add_left 1 _

end E213.Math.Cauchy.EulerSeq

namespace E213.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Math.Cauchy.Archimedean

/-! ### Algebraic invariants -/

/-- **Upper invariant**: 3 * d_n ≥ a_n + 1.  (i.e., S_n ≤ 3 - 1/d_n < 3.) -/
theorem euler_upper_inv (n : Nat) : 3 * eulerDen n ≥ eulerNum n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      show 3 * eulerDen (k + 1) ≥ eulerNum (k + 1) + 1
      show 3 * ((k + 1) * eulerDen k) ≥ (k + 1) * eulerNum k + 1 + 1
      -- 3 * (k+1) * d_k = (k+1) * (3 * d_k) ≥ (k+1) * (a_k + 1)
      --                = (k+1) * a_k + (k+1) ≥ a_{k+1} + 1 + ... ?
      -- (k+1)*a_k + 1 + 1 = a_{k+1} + 1 (since a_{k+1} = (k+1)*a_k + 1)
      -- So we need (k+1)*(3*d_k) ≥ (k+1)*a_k + 2, i.e.,
      -- (k+1)*(3*d_k - a_k) ≥ 2.  By ih: 3*d_k - a_k ≥ 1.
      -- For k+1 ≥ 2 (k ≥ 1): trivial.  For k = 0: 3*d_0 - a_0 = 2.  ✓
      have h_dpos : 1 ≤ eulerDen k := eulerDen_pos k
      have hexp : 3 * ((k + 1) * eulerDen k) = (k + 1) * (3 * eulerDen k) := by
        rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm 3 (k+1), E213.Tactic.Nat213.mul_assoc]
      rw [hexp]
      -- Want: (k+1) * (3 * d_k) ≥ (k+1) * a_k + 2.
      have h1 : (k + 1) * (3 * eulerDen k) ≥ (k + 1) * (eulerNum k + 1) :=
        Nat.mul_le_mul_left (k+1) ih
      have h2 : (k + 1) * (eulerNum k + 1) = (k + 1) * eulerNum k + (k + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [h2] at h1
      -- h1: (k+1)*(3*d_k) ≥ (k+1)*a_k + (k+1)
      -- Goal: (k+1)*(3*d_k) ≥ (k+1)*a_k + 2.
      -- If k ≥ 1 then k+1 ≥ 2, ✓.
      -- If k = 0: ih gives 3*1 ≥ 1 + 1 = 2, so 3*1 - 1 = 2 ≥ ?
      -- Actually for k=0: (k+1)*(3*d_0) = 1*3 = 3.  (k+1)*a_0 + 2 = 1 + 2 = 3.  ≥ ✓.
      by_cases hk : k = 0
      · subst hk
        show 3 * eulerDen 0 ≥ eulerNum 0 + 1 + 1
        decide
      · -- k ≠ 0 → k ≥ 1 → k+1 ≥ 2
        have hk1 : k + 1 ≥ 2 :=
          Nat.succ_le_succ (Nat.pos_of_ne_zero hk)
        -- Goal: (k+1)*(3*d_k) ≥ (k+1)*a_k + 1 + 1
        -- h1: (k+1)*(3*d_k) ≥ (k+1)*a_k + (k+1).
        -- Chain: (k+1)*a_k + 1 + 1 = (k+1)*a_k + 2 ≤ (k+1)*a_k + (k+1) ≤ (k+1)*(3*d_k).
        have h_2_succ : (k+1) * eulerNum k + 1 + 1 = (k+1) * eulerNum k + 2 :=
          Nat.add_assoc _ 1 1
        rw [h_2_succ]
        exact Nat.le_trans (Nat.add_le_add_left hk1 _) h1

end E213.Math.Cauchy.EulerSeq

namespace E213.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Math.Cauchy.Archimedean

/-- **Lower invariant** (n ≥ 2): a_n ≥ 2 * d_n + 1.  (S_n > 2 from n=2.)
    a_2 = 5, d_2 = 2: 5 = 2*2 + 1 ✓.
    Inductive: a_{n+1} = (n+1) * a_n + 1 ≥ (n+1)*(2 d_n + 1) + 1
                       = 2 (n+1) d_n + (n+1) + 1 = 2 d_{n+1} + (n+2). -/
theorem euler_lower_inv (n : Nat) (hn : n ≥ 2) :
    eulerNum n ≥ 2 * eulerDen n + 1 := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      by_cases hk : k = 1
      · subst hk
        show eulerNum 2 ≥ 2 * eulerDen 2 + 1
        decide
      · -- k+1 ≥ 2 means k ≥ 1; with k ≠ 1 we get k ≥ 2
        have hk2 : k ≥ 2 := by
          have hk1 : k ≥ 1 := Nat.le_of_succ_le_succ hn
          cases k with
          | zero => exact absurd hk1 (by decide)
          | succ k' =>
            cases k' with
            | zero => exact absurd rfl hk
            | succ k'' => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k''))
        have h_inv := ih hk2
        show eulerNum (k + 1) ≥ 2 * eulerDen (k + 1) + 1
        show (k + 1) * eulerNum k + 1 ≥ 2 * ((k + 1) * eulerDen k) + 1
        have h1 : (k + 1) * eulerNum k ≥ (k + 1) * (2 * eulerDen k + 1) :=
          Nat.mul_le_mul_left (k+1) h_inv
        have h2 : (k + 1) * (2 * eulerDen k + 1)
                  = 2 * ((k + 1) * eulerDen k) + (k + 1) := by
          rw [Nat.mul_add, Nat.mul_one, ← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (k+1) 2,
              E213.Tactic.Nat213.mul_assoc]
        rw [h2] at h1
        -- h1: (k+1)*a_k ≥ 2*((k+1)*d_k) + (k+1)
        -- Goal: (k+1)*a_k + 1 ≥ 2*((k+1)*d_k) + 1
        -- Chain: 2*((k+1)*d_k) + 1 ≤ 2*((k+1)*d_k) + (k+1) ≤ (k+1)*a_k ≤ (k+1)*a_k + 1
        have hk1 : (k + 1) ≥ 1 := Nat.succ_le_succ (Nat.zero_le _)
        have step1 : 2 * ((k+1) * eulerDen k) + 1
                       ≤ 2 * ((k+1) * eulerDen k) + (k+1) :=
          Nat.add_le_add_left hk1 _
        exact Nat.le_trans (Nat.le_trans step1 h1) (Nat.le_succ _)

end E213.Math.Cauchy.EulerSeq

namespace E213.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Math.Cauchy.Archimedean
open E213.Math.Cauchy.PellSeq

/-! ### Raw sequence + orderProj cuts -/

/-- **Euler Raw sequence**: abLens.view (eulerRaw n) = (eulerNum n, eulerDen n). -/
def eulerRaw (n : Nat) :
    {r : Raw // abLens.view r = (eulerNum n, eulerDen n)} :=
  abLens_witness (eulerNum n + eulerDen n) (eulerNum n) (eulerDen n) rfl
    (eulerNum_pos n) (eulerDen_pos n)

theorem eulerRaw_view (n : Nat) :
    abLens.view (eulerRaw n).val = (eulerNum n, eulerDen n) :=
  (eulerRaw n).property

/-- **Cut above 3**: m/k ≥ 3 (3k ≤ m) → orderProj true (all n).
    a_n * k ≤ (3 d_n - 1) * k ≤ 3 d_n * k ≤ d_n * m. -/
theorem euler_orderProj_above_3 (m k : Nat) (h3km : 3 * k ≤ m) (n : Nat) :
    orderProj m k (abLens.view (eulerRaw n).val) = true := by
  rw [eulerRaw_view]
  show decide (eulerNum n * k ≤ eulerDen n * m) = true
  have hu := euler_upper_inv n
  have h1 : eulerNum n * k ≤ 3 * eulerDen n * k :=
    Nat.mul_le_mul_right k (Nat.le_of_succ_le hu)
  have h2 : 3 * eulerDen n * k = eulerDen n * (3 * k) := by
    rw [Nat.mul_comm 3 (eulerDen n), E213.Tactic.Nat213.mul_assoc]
  rw [h2] at h1
  have h3 : eulerDen n * (3 * k) ≤ eulerDen n * m :=
    Nat.mul_le_mul_left (eulerDen n) h3km
  exact decide_eq_true (Nat.le_trans h1 h3)

end E213.Math.Cauchy.EulerSeq

namespace E213.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Math.Cauchy.Archimedean

/-- **Cut below 2**: m/k ≤ 2 (m ≤ 2k) → orderProj false (n ≥ 2).
    a_n ≥ 2 d_n + 1, so a_n * k ≥ (2 d_n + 1) * k > d_n * m. -/
theorem euler_orderProj_below_2 (m k : Nat) (hk : k ≥ 1) (hm2k : m ≤ 2 * k)
    (n : Nat) (hn : n ≥ 2) :
    orderProj m k (abLens.view (eulerRaw n).val) = false := by
  rw [eulerRaw_view]
  show decide (eulerNum n * k ≤ eulerDen n * m) = false
  apply decide_eq_false
  intro hle
  have hl := euler_lower_inv n hn
  -- hl: a_n ≥ 2 * d_n + 1.
  -- a_n * k ≥ (2 * d_n + 1) * k = 2 d_n k + k.
  -- d_n * m ≤ d_n * (2 k) = 2 d_n k.
  -- So a_n * k ≥ 2 d_n k + k > 2 d_n k ≥ d_n * m.
  have h1 : eulerNum n * k ≥ (2 * eulerDen n + 1) * k :=
    Nat.mul_le_mul_right k hl
  have h2 : (2 * eulerDen n + 1) * k = 2 * eulerDen n * k + k := by
    rw [E213.Tactic.Nat213.add_mul, Nat.one_mul]
  rw [h2] at h1
  have h3 : eulerDen n * m ≤ eulerDen n * (2 * k) :=
    Nat.mul_le_mul_left (eulerDen n) hm2k
  have h4 : eulerDen n * (2 * k) = 2 * eulerDen n * k := by
    rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (eulerDen n) 2, E213.Tactic.Nat213.mul_assoc]
  rw [h4] at h3
  -- h1: a_n * k ≥ 2 d_n k + k.  h3: d_n * m ≤ 2 d_n k.  hle: a_n * k ≤ d_n * m.
  -- Combine: 2 d_n k + k ≤ a_n * k ≤ d_n * m ≤ 2 d_n k.  So k ≤ 0, contra hk.
  have chain : 2 * eulerDen n * k + k ≤ 2 * eulerDen n * k :=
    Nat.le_trans (Nat.le_trans h1 hle) h3
  -- Cancel `2 * eulerDen n * k` from both sides: k ≤ 0.
  have chain_with_zero : 2 * eulerDen n * k + k ≤ 2 * eulerDen n * k + 0 := by
    rw [Nat.add_zero]; exact chain
  have hk0 : k ≤ 0 := E213.Tactic.Nat213.le_of_add_le_add_left chain_with_zero
  exact absurd (Nat.le_trans hk hk0) (by decide)

/-- **Order Cauchy** at thresholds m/k ≥ 3 ∨ m/k ≤ 2.
    Other thresholds in (2, 3) require finer analysis (e ≈ 2.718). -/
theorem euler_orderCauchy_at_concrete (m k : Nat) (hk : k ≥ 1)
    (hcase : 3 * k ≤ m ∨ m ≤ 2 * k) :
    ∃ N, ∀ p q, p ≥ N → q ≥ N →
      orderProj m k (abLens.view (eulerRaw p).val)
        = orderProj m k (abLens.view (eulerRaw q).val) := by
  refine ⟨2, ?_⟩
  intro p q hp hq
  rcases hcase with h3km | hm2k
  · rw [euler_orderProj_above_3 m k h3km p,
        euler_orderProj_above_3 m k h3km q]
  · rw [euler_orderProj_below_2 m k hk hm2k p hp,
        euler_orderProj_below_2 m k hk hm2k q hq]

end E213.Math.Cauchy.EulerSeq

namespace E213.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Math.Cauchy.Archimedean
open E213.Math.Cauchy.MonotonicBounded

/-! ### Monotonicity instance (for MonotonicBoundedCauchy) -/

/-- Euler Raw sequence as `Nat → Raw` (Subtype → Raw projection). -/
def eulerRawSeq : Nat → Raw := fun n => (eulerRaw n).val

/-- Euler seq is ab-monotonic (S_n < S_{n+1}).
    a_n * d_{n+1} = (n+1) * a_n * d_n ≤ (n+1) * a_n * d_n + d_n = a_{n+1} * d_n. -/
theorem euler_isAbMonotonic : IsAbMonotonic eulerRawSeq := by
  intro n
  show (abLens.view (eulerRaw n).val).1 * (abLens.view (eulerRaw (n+1)).val).2
       ≤ (abLens.view (eulerRaw (n+1)).val).1 * (abLens.view (eulerRaw n).val).2
  rw [eulerRaw_view, eulerRaw_view]
  show eulerNum n * eulerDen (n+1) ≤ eulerNum (n+1) * eulerDen n
  show eulerNum n * ((n+1) * eulerDen n) ≤ ((n+1) * eulerNum n + 1) * eulerDen n
  have h1 : eulerNum n * ((n+1) * eulerDen n) = (n+1) * eulerNum n * eulerDen n := by
    rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (eulerNum n) (n+1)]
  rw [h1]
  -- Goal: (n+1) * eulerNum n * eulerDen n ≤ ((n+1) * eulerNum n + 1) * eulerDen n
  exact Nat.mul_le_mul_right (eulerDen n) (Nat.le_add_right _ 1)

/-- Euler seq has positive denominators. -/
theorem euler_isAbPositiveB : IsAbPositiveB eulerRawSeq := by
  intro n
  show 1 ≤ (abLens.view (eulerRaw n).val).2
  rw [eulerRaw_view]
  exact eulerDen_pos n

end E213.Math.Cauchy.EulerSeq
