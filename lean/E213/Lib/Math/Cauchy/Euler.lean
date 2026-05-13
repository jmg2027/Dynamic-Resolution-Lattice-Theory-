import E213.Lib.Math.Cauchy.Archimedean
import E213.Lib.Math.Cauchy.MonotonicBounded
import E213.Lib.Math.Cauchy.PellSeq
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.Nat213

/-!
# Cauchy.Euler — e (Euler) Dedekind cut + sharper bounds + generic template

Consolidated Euler-cut family (CLAUDE.md rule 7):

| Section | Topic |
|---|---|
| `EulerSeq` | Σ 1/k! partial sums foundation |
| `EulerSharper` | e > 5/2 strict bound |
| `EulerSharperKernelFree` | propext-reduced variant |
| `EulerSharperPure` | e > 8/3 strict, fully ∅-axiom |
| `EulerGenericPure` | parametric template for arbitrary b |
| `EulerCombinatorialPure` | combinatorial Euler bounds |

Per-section namespaces preserved.  PURE 진화: Seq → Sharper →
KernelFree → Pure (final ∅-axiom form).
-/

namespace E213.Lib.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean
open E213.Lib.Math.Cauchy.PellSeq

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

end E213.Lib.Math.Cauchy.EulerSeq

namespace E213.Lib.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

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

end E213.Lib.Math.Cauchy.EulerSeq

namespace E213.Lib.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

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

end E213.Lib.Math.Cauchy.EulerSeq

namespace E213.Lib.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean
open E213.Lib.Math.Cauchy.PellSeq

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

end E213.Lib.Math.Cauchy.EulerSeq

namespace E213.Lib.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

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

end E213.Lib.Math.Cauchy.EulerSeq

namespace E213.Lib.Math.Cauchy.EulerSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean
open E213.Lib.Math.Cauchy.MonotonicBounded

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

end E213.Lib.Math.Cauchy.EulerSeq

namespace E213.Lib.Math.Cauchy.EulerSharper

open E213.Theory E213.Lens
open E213.Lib.Math.Cauchy.EulerSeq

/-- **e > 5/2 strict** (n ≥ 3): 2 * eulerNum n ≥ 5 * eulerDen n + 1. -/
theorem euler_sharper_lower (n : Nat) (hn : n ≥ 3) :
    2 * eulerNum n ≥ 5 * eulerDen n + 1 := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      by_cases hk : k = 2
      · subst hk
        show 2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1
        decide
      · have hk3 : k ≥ 3 :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hn) (Ne.symm hk)
        have h_inv := ih hk3
        show 2 * eulerNum (k + 1) ≥ 5 * eulerDen (k + 1) + 1
        show 2 * ((k + 1) * eulerNum k + 1) ≥ 5 * ((k + 1) * eulerDen k) + 1
        have h1 : 2 * ((k + 1) * eulerNum k) ≥
                  (k + 1) * (5 * eulerDen k + 1) := by
          have step : 2 * ((k + 1) * eulerNum k) =
                      (k + 1) * (2 * eulerNum k) := by
            rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm 2 (k+1), E213.Tactic.Nat213.mul_assoc]
          rw [step]
          exact Nat.mul_le_mul_left (k+1) h_inv
        have h2 : (k + 1) * (5 * eulerDen k + 1)
                  = 5 * ((k + 1) * eulerDen k) + (k + 1) := by
          rw [Nat.mul_add, Nat.mul_one, ← E213.Tactic.Nat213.mul_assoc,
              Nat.mul_comm (k+1) 5, E213.Tactic.Nat213.mul_assoc]
        -- h1 : (k+1) * (5*eulerDen k + 1) ≤ 2 * ((k+1) * eulerNum k)
        -- h2 says LHS = 5 * ((k+1)*eulerDen k) + (k+1)
        -- Goal: 5 * ((k+1)*eulerDen k) + 1 ≤ 2 * ((k+1)*eulerNum k + 1)
        --                              = 2*(k+1)*eulerNum k + 2
        have h1' : 5 * ((k+1) * eulerDen k) + (k+1) ≤
                   2 * ((k+1) * eulerNum k) := h2 ▸ h1
        have hge2 : 2 ≤ k + 1 :=
          Nat.le_trans (by decide : 2 ≤ 4) (Nat.succ_le_succ hk3)
        -- 5 * X + 1 ≤ 5*X + (k+1) ≤ 2 * Y, want 5*X + 1 ≤ 2*Y + 2
        have : 5 * ((k+1) * eulerDen k) + 1 ≤ 2 * ((k+1) * eulerNum k) :=
          Nat.le_trans (Nat.add_le_add_left
            (Nat.le_trans (by decide : 1 ≤ 2) hge2) _) h1'
        -- Goal: 5 * ((k+1)*eulerDen k) + 1 ≤ 2 * ((k+1)*eulerNum k + 1)
        -- 2 * ((k+1)*eulerNum k + 1) = 2*(k+1)*eulerNum k + 2
        --                            = (2*(k+1)*eulerNum k) + 2
        have hgoal_eq : 2 * ((k+1) * eulerNum k + 1)
                      = 2 * ((k+1) * eulerNum k) + 2 := Nat.mul_add 2 _ 1
        exact hgoal_eq.symm ▸ Nat.le_trans this (Nat.le_add_right _ 2)

end E213.Lib.Math.Cauchy.EulerSharper

namespace E213.Lib.Math.Cauchy.EulerSharperKernelFree

open E213.Lib.Math.Cauchy.EulerSeq

/-- **e > 5/2 strict at n = 3** (axiom-free base case): 2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1.
    Concrete value check via `decide`. -/
theorem euler_sharper_lower_n3 :
    2 * eulerNum 3 ≥ 5 * eulerDen 3 + 1 := by
  decide

/-- Same at n = 4. -/
theorem euler_sharper_lower_n4 :
    2 * eulerNum 4 ≥ 5 * eulerDen 4 + 1 := by
  decide

end E213.Lib.Math.Cauchy.EulerSharperKernelFree

namespace E213.Lib.Math.Cauchy.EulerCombinatorialPure

open E213.Meta.Nat.PureNat
open E213.Lib.Math.Cauchy.EulerSeq

/-- **Euler upper bound, axiom-free**: 3 * eulerDen n ≥ eulerNum n + 1.
    No omega — manual Nat reasoning.

    Base cases n=0, n=1 directly by decide.  n=k+1 for k ≥ 1: IH * (k+1)
    + slack chain. -/
theorem euler_upper_pure (n : Nat) : 3 * eulerDen n ≥ eulerNum n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      match k with
      | 0 => decide  -- n = 1
      | k_pred + 1 =>
          -- k = k_pred + 1 ≥ 1, so (k+1) = k_pred + 2 ≥ 2.
          show 3 * eulerDen (k_pred + 1 + 1) ≥ eulerNum (k_pred + 1 + 1) + 1
          show 3 * ((k_pred + 1 + 1) * eulerDen (k_pred + 1)) ≥
               (k_pred + 1 + 1) * eulerNum (k_pred + 1) + 1 + 1
          have h_assoc : 3 * ((k_pred+1+1) * eulerDen (k_pred+1))
                       = (k_pred+1+1) * (3 * eulerDen (k_pred+1)) := by
            rw [← mul_assoc, Nat.mul_comm 3 (k_pred+1+1), mul_assoc]
          rw [h_assoc]
          have h_mul : (k_pred+1+1) * (3 * eulerDen (k_pred+1)) ≥
                       (k_pred+1+1) * (eulerNum (k_pred+1) + 1) :=
            Nat.mul_le_mul_left (k_pred+1+1) ih
          have h_distrib : (k_pred+1+1) * (eulerNum (k_pred+1) + 1)
                         = (k_pred+1+1) * eulerNum (k_pred+1) + (k_pred+1+1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [h_distrib] at h_mul
          have h_ge_2 : k_pred + 1 + 1 ≥ 2 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have h_target : (k_pred+1+1) * eulerNum (k_pred+1) + (k_pred+1+1) ≥
                          (k_pred+1+1) * eulerNum (k_pred+1) + 1 + 1 := by
            rw [Nat.add_assoc]
            exact Nat.add_le_add_left h_ge_2 _
          exact Nat.le_trans h_target h_mul

/-- **Euler lower bound, axiom-free**: n ≥ 2 → eulerNum n ≥ 2 * eulerDen n + 1.
    (S_n > 2 strict for n ≥ 2.) -/
theorem euler_lower_pure (n : Nat) (hn : n ≥ 2) :
    eulerNum n ≥ 2 * eulerDen n + 1 := by
  induction n with
  | zero =>
      exfalso; exact Nat.not_succ_le_zero 1 hn
  | succ k ih =>
      match k with
      | 0 =>
          exfalso
          have : 1 ≤ 0 := Nat.le_of_succ_le_succ hn
          exact Nat.not_succ_le_zero 0 this
      | 1 =>
          decide
      | k_pred + 2 =>
          have hk2 : k_pred + 2 ≥ 2 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have h_inv := ih hk2
          show eulerNum (k_pred + 2 + 1) ≥ 2 * eulerDen (k_pred + 2 + 1) + 1
          show (k_pred+2+1) * eulerNum (k_pred+2) + 1 ≥
               2 * ((k_pred+2+1) * eulerDen (k_pred+2)) + 1
          have h_assoc : 2 * ((k_pred+2+1) * eulerDen (k_pred+2))
                       = (k_pred+2+1) * (2 * eulerDen (k_pred+2)) := by
            rw [← mul_assoc, Nat.mul_comm 2 (k_pred+2+1), mul_assoc]
          rw [h_assoc]
          have h_mul : (k_pred+2+1) * eulerNum (k_pred+2) ≥
                       (k_pred+2+1) * (2 * eulerDen (k_pred+2) + 1) :=
            Nat.mul_le_mul_left (k_pred+2+1) h_inv
          have h_distrib : (k_pred+2+1) * (2 * eulerDen (k_pred+2) + 1)
                         = (k_pred+2+1) * (2 * eulerDen (k_pred+2)) + (k_pred+2+1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [h_distrib] at h_mul
          -- h_mul : (k+1) * eulerNum k ≥ (k+1) * (2 * eulerDen k) + (k+1)
          -- Drop the +(k+1) → ≥ (k+1) * (2 * eulerDen k)
          have h_drop : (k_pred+2+1) * (2 * eulerDen (k_pred+2)) + (k_pred+2+1) ≥
                        (k_pred+2+1) * (2 * eulerDen (k_pred+2)) :=
            Nat.le_add_right _ _
          have h_chain : (k_pred+2+1) * eulerNum (k_pred+2) ≥
                         (k_pred+2+1) * (2 * eulerDen (k_pred+2)) :=
            Nat.le_trans h_drop h_mul
          exact Nat.add_le_add_right h_chain 1

/-- **Combinatorial Hermite-direction**: 2 < S_n < 3 strict for n ≥ 2.
    The *first integer constraint* on e — no a/b fits this cut
    (mod-2 form of e ≠ a/b for b ≥ 1).

    Specifically: `2 * eulerDen n < eulerNum n` AND `3 * eulerDen n
    > eulerNum n` for n ≥ 2.  Hence S_n ∈ (2, 3) strict. -/
theorem euler_in_open_2_3 (n : Nat) (hn : n ≥ 2) :
    2 * eulerDen n < eulerNum n ∧ eulerNum n < 3 * eulerDen n := by
  refine ⟨?_, ?_⟩
  · -- 2 * eulerDen n < eulerNum n.  From euler_lower: eulerNum ≥ 2*eulerDen + 1.
    have := euler_lower_pure n hn
    exact Nat.lt_of_succ_le this
  · -- eulerNum n < 3 * eulerDen n.  From euler_upper: 3*eulerDen ≥ eulerNum + 1.
    have := euler_upper_pure n
    exact Nat.lt_of_succ_le this

end E213.Lib.Math.Cauchy.EulerCombinatorialPure
namespace E213.Lib.Math.Cauchy.EulerSharperPure

open E213.Meta.Nat.PureNat
open E213.Lib.Math.Cauchy.EulerSeq

/-- **e > 8/3 strict** (n ≥ 4): 3 * eulerNum n ≥ 8 * eulerDen n + 1.

    Inductive base n=4: 3·65 = 195 ≥ 193 = 8·24 + 1.
    Step: IH * (k+1) + arithmetic. -/
theorem euler_sharper_8_3_pure (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≥ 8 * eulerDen n + 1 := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      match k with
      | 0 => exact absurd hn (by decide)
      | 1 => exact absurd hn (by decide)
      | 2 => exact absurd hn (by decide)
      | 3 => decide  -- n = 4
      | k_pred + 4 =>
          have hk4 : k_pred + 4 ≥ 4 := Nat.le_add_left 4 k_pred
          have h_inv := ih hk4
          show 3 * ((k_pred + 4 + 1) * eulerNum (k_pred + 4) + 1) ≥
               8 * ((k_pred + 4 + 1) * eulerDen (k_pred + 4)) + 1
          have h_lhs : 3 * ((k_pred+4+1) * eulerNum (k_pred+4) + 1)
                     = (k_pred+4+1) * (3 * eulerNum (k_pred+4)) + 3 := by
            rw [Nat.mul_add, Nat.mul_one, ← mul_assoc,
                Nat.mul_comm 3 (k_pred+4+1), mul_assoc]
          have h_rhs : 8 * ((k_pred+4+1) * eulerDen (k_pred+4)) + 1
                     = (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 1 := by
            rw [← mul_assoc, Nat.mul_comm 8 (k_pred+4+1), mul_assoc]
          rw [h_lhs, h_rhs]
          have h_mul : (k_pred+4+1) * (3 * eulerNum (k_pred+4)) ≥
                       (k_pred+4+1) * (8 * eulerDen (k_pred+4) + 1) :=
            Nat.mul_le_mul_left (k_pred+4+1) h_inv
          have h_dist : (k_pred+4+1) * (8 * eulerDen (k_pred+4) + 1) =
                        (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + (k_pred+4+1) := by
            rw [Nat.mul_add, Nat.mul_one]
          rw [h_dist] at h_mul
          have h_drop : (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + (k_pred+4+1) ≥
                        (k_pred+4+1) * (8 * eulerDen (k_pred+4)) :=
            Nat.le_add_right _ _
          have h_chain : (k_pred+4+1) * (3 * eulerNum (k_pred+4)) ≥
                         (k_pred+4+1) * (8 * eulerDen (k_pred+4)) :=
            Nat.le_trans h_drop h_mul
          have h_add3 : (k_pred+4+1) * (3 * eulerNum (k_pred+4)) + 3 ≥
                        (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 3 :=
            Nat.add_le_add_right h_chain 3
          have h_31 : (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 3 ≥
                      (k_pred+4+1) * (8 * eulerDen (k_pred+4)) + 1 := by
            apply Nat.add_le_add_left
            decide
          exact Nat.le_trans h_31 h_add3

/-- eulerDen N ≥ 1, axiom-free version. -/
theorem eulerDen_pos_pure (N : Nat) : eulerDen N ≥ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
      show eulerDen (k + 1) ≥ 1
      show (k + 1) * eulerDen k ≥ 1
      have h_kp : k + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_mul : (k + 1) * eulerDen k ≥ (k + 1) * 1 :=
        Nat.mul_le_mul_left (k+1) ih
      rw [Nat.mul_one] at h_mul
      exact Nat.le_trans h_kp h_mul

/-- **e ≠ a/3 (partial sum form, axiom-free)**: for every N ≥ 4
    and positive integer a, `3 · eulerNum N ≠ a · eulerDen N`.

    A statement about the framework's partial sums.  In the limit
    sense S_N → e, this formalizes e ≠ a/3 for any a ∈ ℕ⁺.
    Framework-internal formalization of a Hermite-style proof. -/
theorem e_partial_neq_third_a (a : Nat) (ha : a ≥ 1) (N : Nat) (hN : N ≥ 4) :
    3 * eulerNum N ≠ a * eulerDen N := by
  intro heq
  have h_lower : 3 * eulerNum N ≥ 8 * eulerDen N + 1 :=
    euler_sharper_8_3_pure N hN
  have h_upper : 3 * eulerDen N ≥ eulerNum N + 1 :=
    EulerCombinatorialPure.euler_upper_pure N
  -- From upper: eulerNum N + 1 ≤ 3 * eulerDen N, so eulerNum N ≤ 3 * eulerDen N - 1.
  -- Multiply by 3: 3 * eulerNum N ≤ 9 * eulerDen N - 3.
  have h_upper3 : 3 * eulerNum N + 3 ≤ 9 * eulerDen N := by
    have h1 : 3 * (eulerNum N + 1) ≤ 3 * (3 * eulerDen N) :=
      Nat.mul_le_mul_left 3 h_upper
    have h2 : 3 * (3 * eulerDen N) = 9 * eulerDen N :=
      (E213.Tactic.Nat213.mul_assoc 3 3 (eulerDen N)).symm
    have h3 : 3 * (eulerNum N + 1) = 3 * eulerNum N + 3 := by
      rw [Nat.mul_add, Nat.mul_one]
    exact h2 ▸ h3 ▸ h1
  -- Now: heq : 3 * eulerNum N = a * eulerDen N
  -- h_lower: a * eulerDen N ≥ 8 * eulerDen N + 1
  -- h_upper3: a * eulerDen N + 3 ≤ 9 * eulerDen N
  rw [heq] at h_lower h_upper3
  -- h_lower: a * eulerDen N ≥ 8 * eulerDen N + 1 → a ≥ 9 (if eulerDen N ≥ 1)
  -- h_upper3: a * eulerDen N ≤ 9 * eulerDen N - 3 → a ≤ 8 (similar)
  have hd_pos : eulerDen N ≥ 1 := eulerDen_pos_pure N
  -- From h_lower: a * eulerDen N ≥ 8 * eulerDen N + 1
  -- Suppose a ≤ 8.  Then a * eulerDen N ≤ 8 * eulerDen N.
  -- But ≥ 8 * eulerDen N + 1, contradiction.
  -- So a ≥ 9.
  have h_a_ge_9 : a ≥ 9 := by
    rcases Nat.lt_or_ge a 9 with h_lt | h_ge
    · exfalso
      have h_a_le_8 : a ≤ 8 := Nat.le_of_lt_succ h_lt
      have h_amul : a * eulerDen N ≤ 8 * eulerDen N :=
        Nat.mul_le_mul_right (eulerDen N) h_a_le_8
      have : 8 * eulerDen N + 1 ≤ 8 * eulerDen N :=
        Nat.le_trans h_lower h_amul
      exact Nat.not_succ_le_self (8 * eulerDen N) this
    · exact h_ge
  -- From h_upper3: a * eulerDen N + 3 ≤ 9 * eulerDen N
  -- Suppose a ≥ 9.  Then a * eulerDen N ≥ 9 * eulerDen N.
  -- a * eulerDen N + 3 ≥ 9 * eulerDen N + 3 > 9 * eulerDen N.
  -- Contradicts h_upper3.
  have h_amul9 : a * eulerDen N ≥ 9 * eulerDen N :=
    Nat.mul_le_mul_right (eulerDen N) h_a_ge_9
  have h_plus3 : a * eulerDen N + 3 ≥ 9 * eulerDen N + 3 :=
    Nat.add_le_add_right h_amul9 3
  have hcontra : 9 * eulerDen N + 3 ≤ 9 * eulerDen N :=
    Nat.le_trans h_plus3 h_upper3
  -- 9 * eulerDen N + 3 ≤ 9 * eulerDen N means 3 ≤ 0, false.
  have h3le0 : 3 ≤ 0 := E213.Tactic.Nat213.le_of_add_le_add_left hcontra
  exact Nat.not_succ_le_zero 2 h3le0

end E213.Lib.Math.Cauchy.EulerSharperPure
namespace E213.Lib.Math.Cauchy.EulerGenericPure

open E213.Meta.Nat.PureNat
open E213.Lib.Math.Cauchy.EulerSeq

/-- **Inductive step lemma**: IH `b · a_k ≥ j · d_k + 1` →
    `b · a_{k+1} ≥ j · d_{k+1} + 1`.

    Pure arithmetic chain, no omega. -/
theorem euler_lower_step (j b k : Nat) (hb : b ≥ 1)
    (h_inv : b * eulerNum k ≥ j * eulerDen k + 1) :
    b * eulerNum (k + 1) ≥ j * eulerDen (k + 1) + 1 := by
  show b * ((k + 1) * eulerNum k + 1) ≥ j * ((k + 1) * eulerDen k) + 1
  -- LHS = (k+1) * (b * eulerNum k) + b
  -- RHS = (k+1) * (j * eulerDen k) + 1
  have h_lhs : b * ((k+1) * eulerNum k + 1) = (k+1) * (b * eulerNum k) + b := by
    rw [Nat.mul_add, Nat.mul_one, ← mul_assoc, Nat.mul_comm b (k+1), mul_assoc]
  have h_rhs : j * ((k+1) * eulerDen k) = (k+1) * (j * eulerDen k) := by
    rw [← mul_assoc, Nat.mul_comm j (k+1), mul_assoc]
  rw [h_lhs, h_rhs]
  have h_mul : (k+1) * (b * eulerNum k) ≥ (k+1) * (j * eulerDen k + 1) :=
    Nat.mul_le_mul_left (k+1) h_inv
  have h_dist : (k+1) * (j * eulerDen k + 1)
              = (k+1) * (j * eulerDen k) + (k+1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h_dist] at h_mul
  -- h_mul : (k+1) * (b * eulerNum k) ≥ (k+1) * (j * eulerDen k) + (k+1)
  -- Need: (k+1) * (b * eulerNum k) + b ≥ (k+1) * (j * eulerDen k) + 1
  have h_add_b : (k+1) * (b * eulerNum k) + b ≥
                 (k+1) * (j * eulerDen k) + (k+1) + b :=
    Nat.add_le_add_right h_mul b
  have h_drop : (k+1) * (j * eulerDen k) + (k+1) + b ≥
                (k+1) * (j * eulerDen k) + 1 := by
    rw [Nat.add_assoc]
    apply Nat.add_le_add_left
    -- (k+1) + b ≥ 1 (since both ≥ 1)
    have : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact Nat.le_trans this (Nat.le_add_right (k+1) b)
  exact Nat.le_trans h_drop h_add_b

/-- **Generic Euler lower bound (META-ALGORITHM)**: ∀ j b (b ≥ 1)
    N0, given only a base case verification, ∀ n ≥ N0,
    `b · eulerNum n ≥ j · eulerDen n + 1` (== S_n > j/b strict).

    Argument: only the per-(j, b) base case needs `decide` to verify. -/
theorem euler_lower_generic (j b N0 : Nat) (hb : b ≥ 1)
    (h_base : b * eulerNum N0 ≥ j * eulerDen N0 + 1) :
    ∀ n, n ≥ N0 → b * eulerNum n ≥ j * eulerDen n + 1 := by
  intro n hn
  -- Induction on (n - N0) via auxiliary form.
  induction n with
  | zero =>
      have hN0 : N0 = 0 := Nat.le_zero.mp hn
      rw [hN0] at h_base
      exact h_base
  | succ k ih =>
      rcases Nat.lt_or_ge k N0 with h_lt | h_ge
      · -- k < N0, so k + 1 = N0 (since k + 1 ≥ N0)
        have h_kp1 : k + 1 = N0 := by
          have h1 : N0 ≤ k + 1 := hn
          have h2 : k + 1 ≤ N0 := h_lt
          exact Nat.le_antisymm h2 h1
        rw [h_kp1]
        exact h_base
      · have h_inv := ih h_ge
        exact euler_lower_step j b k hb h_inv

/-! ### Per-b applications via meta-algorithm -/

/-- e > 8/3 strict (b=3, j=8, N0=4). -/
theorem e_gt_8_3 (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≥ 8 * eulerDen n + 1 :=
  euler_lower_generic 8 3 4 (by decide) (by decide) n hn

/-- e > 10/4 = 5/2 strict (b=4, j=10, N0=4). -/
theorem e_gt_10_4 (n : Nat) (hn : n ≥ 4) :
    4 * eulerNum n ≥ 10 * eulerDen n + 1 :=
  euler_lower_generic 10 4 4 (by decide) (by decide) n hn

/-- e > 13/5 strict (b=5, j=13, N0=5). -/
theorem e_gt_13_5 (n : Nat) (hn : n ≥ 5) :
    5 * eulerNum n ≥ 13 * eulerDen n + 1 :=
  euler_lower_generic 13 5 5 (by decide) (by decide) n hn

/-- e > 19/7 strict (b=7, j=19, N0=6).  e ≈ 2.718, 19/7 ≈ 2.714. -/
theorem e_gt_19_7 (n : Nat) (hn : n ≥ 6) :
    7 * eulerNum n ≥ 19 * eulerDen n + 1 :=
  euler_lower_generic 19 7 6 (by decide) (by decide) n hn

/-! ### Upper bound meta-algorithm (symmetric) -/

/-- Inductive step for upper bound: `j · eulerDen k ≥ b · eulerNum k + 1`
    AND `k ≥ b` → `j · eulerDen (k+1) ≥ b · eulerNum (k+1) + 1`. -/
theorem euler_upper_step (j b k : Nat) (hk : k ≥ b)
    (h_inv : j * eulerDen k ≥ b * eulerNum k + 1) :
    j * eulerDen (k + 1) ≥ b * eulerNum (k + 1) + 1 := by
  show j * ((k + 1) * eulerDen k) ≥ b * ((k + 1) * eulerNum k + 1) + 1
  have h_lhs : j * ((k+1) * eulerDen k) = (k+1) * (j * eulerDen k) := by
    rw [← mul_assoc, Nat.mul_comm j (k+1), mul_assoc]
  have h_rhs : b * ((k+1) * eulerNum k + 1) + 1
             = (k+1) * (b * eulerNum k) + b + 1 := by
    rw [Nat.mul_add, Nat.mul_one, ← mul_assoc, Nat.mul_comm b (k+1), mul_assoc]
  rw [h_lhs, h_rhs]
  have h_mul : (k+1) * (j * eulerDen k) ≥ (k+1) * (b * eulerNum k + 1) :=
    Nat.mul_le_mul_left (k+1) h_inv
  have h_dist : (k+1) * (b * eulerNum k + 1)
              = (k+1) * (b * eulerNum k) + (k+1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [h_dist] at h_mul
  -- Need: (k+1) * (j · d_k) ≥ (k+1) * (b · a_k) + b + 1
  -- Have: (k+1) * (j · d_k) ≥ (k+1) * (b · a_k) + (k+1)
  -- So need (k+1) ≥ b + 1, i.e., k ≥ b.
  have h_kp1_ge : k + 1 ≥ b + 1 := Nat.succ_le_succ hk
  have h_target : (k+1) * (b * eulerNum k) + (k+1) ≥
                  (k+1) * (b * eulerNum k) + (b + 1) :=
    Nat.add_le_add_left h_kp1_ge _
  have h_unfold : (k+1) * (b * eulerNum k) + (b + 1)
                = (k+1) * (b * eulerNum k) + b + 1 := by
    rw [Nat.add_assoc]
  rw [h_unfold] at h_target
  exact Nat.le_trans h_target h_mul

/-- **Generic Euler upper bound (META-ALGORITHM)**: `S_n < j/b` strict
    for n ≥ max(N0, b). -/
theorem euler_upper_generic (j b N0 : Nat) (hb : b ≥ 1) (hN0 : N0 ≥ b)
    (h_base : j * eulerDen N0 ≥ b * eulerNum N0 + 1) :
    ∀ n, n ≥ N0 → j * eulerDen n ≥ b * eulerNum n + 1 := by
  intro n hn
  induction n with
  | zero =>
      have hN0_zero : N0 = 0 := Nat.le_zero.mp hn
      rw [hN0_zero] at h_base
      exact h_base
  | succ k ih =>
      rcases Nat.lt_or_ge k N0 with h_lt | h_ge
      · have h_kp1 : k + 1 = N0 := by
          have h2 : k + 1 ≤ N0 := h_lt
          exact Nat.le_antisymm h2 hn
        rw [h_kp1]; exact h_base
      · have h_inv := ih h_ge
        have h_k_ge_b : k ≥ b := Nat.le_trans hN0 h_ge
        exact euler_upper_step j b k h_k_ge_b h_inv

/-- Per-b upper: e < 9/3 = 3 (b=3, j=9, N0=3). -/
theorem e_lt_9_3 (n : Nat) (hn : n ≥ 3) :
    9 * eulerDen n ≥ 3 * eulerNum n + 1 :=
  euler_upper_generic 9 3 3 (by decide) (by decide) (by decide) n hn

/-- Per-b upper: e < 11/4 (b=4, j=11, N0=4). -/
theorem e_lt_11_4 (n : Nat) (hn : n ≥ 4) :
    11 * eulerDen n ≥ 4 * eulerNum n + 1 :=
  euler_upper_generic 11 4 4 (by decide) (by decide) (by decide) n hn

/-! ### Transcendental cut discriminator

Combination of `euler_lower_generic` + `euler_upper_generic` —
a unified theorem for e-discrimination for arbitrary (a, b). -/

/-- **Transcendental cut discriminator (lower side)**: for arbitrary
    (a, b), if there is a sharper lower with j_low ≥ a, then S_n > a/b
    strict for all n ≥ N0.

    Partial-sum form of e > a/b. -/
theorem e_partial_gt_a_b (a b j_low N0 : Nat) (hb : b ≥ 1)
    (h_a_le_j : a ≤ j_low)
    (h_base : b * eulerNum N0 ≥ j_low * eulerDen N0 + 1) :
    ∀ n, n ≥ N0 → b * eulerNum n > a * eulerDen n := by
  intro n hn
  have h_lower := euler_lower_generic j_low b N0 hb h_base n hn
  -- h_lower : b · eulerNum n ≥ j_low · eulerDen n + 1
  -- a ≤ j_low → a · eulerDen n ≤ j_low · eulerDen n
  have h_amul : a * eulerDen n ≤ j_low * eulerDen n :=
    Nat.mul_le_mul_right (eulerDen n) h_a_le_j
  -- b · eulerNum n ≥ j_low · eulerDen n + 1 > j_low · eulerDen n ≥ a · eulerDen n
  have h_strict : j_low * eulerDen n + 1 > a * eulerDen n :=
    Nat.lt_succ_of_le h_amul
  exact Nat.lt_of_lt_of_le h_strict h_lower

/-- **Transcendental cut discriminator (upper side)**: if there is a
    sharper upper with a ≥ j_up, then S_n < a/b strict for all n ≥ N0.

    Partial-sum form of e < a/b. -/
theorem e_partial_lt_a_b (a b j_up N0 : Nat) (hb : b ≥ 1) (hN0 : N0 ≥ b)
    (h_a_ge_j : a ≥ j_up)
    (h_base : j_up * eulerDen N0 ≥ b * eulerNum N0 + 1) :
    ∀ n, n ≥ N0 → a * eulerDen n > b * eulerNum n := by
  intro n hn
  have h_upper := euler_upper_generic j_up b N0 hb hN0 h_base n hn
  -- h_upper : j_up · eulerDen n ≥ b · eulerNum n + 1
  have h_amul : a * eulerDen n ≥ j_up * eulerDen n :=
    Nat.mul_le_mul_right (eulerDen n) h_a_ge_j
  have h_strict : a * eulerDen n + 1 > b * eulerNum n + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans h_upper h_amul)
  exact Nat.lt_of_succ_lt_succ h_strict

/-- **e ≠ a/b** (partial-sum form): if a/b is outside the (j_low, j_up)
    interval, then e ≠ a/b in framework partial sum form. -/
theorem e_partial_neq_a_b (a b j_low j_up N0 : Nat) (hb : b ≥ 1) (hN0 : N0 ≥ b)
    (h_a_out : a ≤ j_low ∨ a ≥ j_up)
    (h_lower_base : b * eulerNum N0 ≥ j_low * eulerDen N0 + 1)
    (h_upper_base : j_up * eulerDen N0 ≥ b * eulerNum N0 + 1) :
    ∀ n, n ≥ N0 → b * eulerNum n ≠ a * eulerDen n := by
  intro n hn heq
  cases h_a_out with
  | inl h_le =>
      have h_gt := e_partial_gt_a_b a b j_low N0 hb h_le h_lower_base n hn
      rw [heq] at h_gt
      exact Nat.lt_irrefl _ h_gt
  | inr h_ge =>
      have h_lt := e_partial_lt_a_b a b j_up N0 hb hN0 h_ge h_upper_base n hn
      rw [heq] at h_lt
      exact Nat.lt_irrefl _ h_lt

/-! ### Demonstrations: e ≠ a/b for fixed b, all a -/

/-- **e ≠ a/3 for any a** via unified discriminator (j_low=8, j_up=9). -/
theorem e_neq_a_third (a : Nat) (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≠ a * eulerDen n := by
  apply e_partial_neq_a_b a 3 8 9 4 (by decide) (by decide) ?_
    (by decide) (by decide) n hn
  -- a ≤ 8 ∨ a ≥ 9
  rcases Nat.lt_or_ge a 9 with h | h
  · exact Or.inl (Nat.le_of_lt_succ h)
  · exact Or.inr h

/-- **e ≠ a/4 for any a** via unified discriminator (j_low=10, j_up=11). -/
theorem e_neq_a_quarter (a : Nat) (n : Nat) (hn : n ≥ 4) :
    4 * eulerNum n ≠ a * eulerDen n := by
  apply e_partial_neq_a_b a 4 10 11 4 (by decide) (by decide) ?_
    (by decide) (by decide) n hn
  rcases Nat.lt_or_ge a 11 with h | h
  · exact Or.inl (Nat.le_of_lt_succ h)
  · exact Or.inr h

end E213.Lib.Math.Cauchy.EulerGenericPure
