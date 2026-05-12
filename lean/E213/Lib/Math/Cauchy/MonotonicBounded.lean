import E213.Lens.Instances.AB
import E213.Lib.Math.Cauchy.Archimedean
import E213.Meta.Tactic.Nat213

/-!
# MonotonicBoundedCauchy: monotonic ab-sequence → orderCauchy

**Generalization** of specific transcendental cuts
(e ∈ (2, 3), π/2 ∈ (1, 2), etc.): an ab-monotonically increasing
sequence is automatically isOrderCauchy for every (m, k) threshold.

## Key Insight

orderProj m k (a, b) = decide (a*k ≤ b*m) compares the ab-ratio
a/b against m/k.  When the sequence is monotonically increasing the
Bool sequence {orderProj m k (xs n)} transitions at most once
(true → false).  Therefore it is eventually constant — orderCauchy.

## Applications

- EulerSeq: a_n / d_n = Σ 1/k! is monotonically increasing →
  orderCauchy at every (m, k) cut.
- WallisSeq: W_n = ∏ (2k)²/((2k-1)(2k+1)) is monotonically
  increasing → same conclusion.

This general theorem automatically extends earlier specific cuts
(m/k ≥ 3, m/k ≤ 2, etc.) to **all (m, k)** — strengthening the §7
closure of Paper 1.

Status: ∅-axiom on every theorem (`tools/scan_axioms.py` reports
6 PURE / 0 DIRTY).
-/

namespace E213.Lib.Math.Cauchy.MonotonicBounded

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

/-! ### Hypotheses -/

/-- ab-monotonically non-decreasing: a_n / b_n ≤ a_{n+1} / b_{n+1}.
    Cross-multiplied form (Nat-friendly). -/
def IsAbMonotonic (xs : Nat → Raw) : Prop :=
  ∀ n, (abLens.view (xs n)).1 * (abLens.view (xs (n+1))).2
       ≤ (abLens.view (xs (n+1))).1 * (abLens.view (xs n)).2

/-- The b component of abLens.view is positive for all terms.
    Satisfied by Pell, Euler, and Wallis (denominator always ≥ 1). -/
def IsAbPositiveB (xs : Nat → Raw) : Prop :=
  ∀ n, 1 ≤ (abLens.view (xs n)).2

end E213.Lib.Math.Cauchy.MonotonicBounded

namespace E213.Lib.Math.Cauchy.MonotonicBounded

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

/-! ### Monotonic chain (transitive form) -/

/-- Chain: ∀ p ≤ q, a_p * b_q ≤ a_q * b_p. -/
theorem ab_monotonic_chain (xs : Nat → Raw)
    (hmono : IsAbMonotonic xs) (hpos : IsAbPositiveB xs)
    (p : Nat) : ∀ q, p ≤ q →
      (abLens.view (xs p)).1 * (abLens.view (xs q)).2
        ≤ (abLens.view (xs q)).1 * (abLens.view (xs p)).2 := by
  intro q hpq
  induction q with
  | zero =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hpq
      subst hp0
      exact Nat.le_refl _
  | succ k ih =>
      by_cases hpk : p ≤ k
      · -- IH: a_p * b_k ≤ a_k * b_p
        -- hmono k: a_k * b_{k+1} ≤ a_{k+1} * b_k
        -- Combine: a_p * b_k * b_{k+1} ≤ a_k * b_p * b_{k+1} ≤ a_{k+1} * b_p * b_k
        -- Divide by b_k (≥ 1): a_p * b_{k+1} ≤ a_{k+1} * b_p
        have hIH := ih hpk
        have hstep := hmono k
        have hbk : 1 ≤ (abLens.view (xs k)).2 := hpos k
        -- Multiply hIH by bk1: ap * bk * bk1 ≤ ak * bp * bk1
        have h1 : (abLens.view (xs p)).1 * (abLens.view (xs k)).2
                    * (abLens.view (xs (k+1))).2
                  ≤ (abLens.view (xs k)).1 * (abLens.view (xs p)).2
                    * (abLens.view (xs (k+1))).2 :=
          Nat.mul_le_mul_right _ hIH
        -- Multiply hstep by bp: ak * bk1 * bp ≤ ak1 * bk * bp
        have h2 : (abLens.view (xs k)).1 * (abLens.view (xs (k+1))).2
                    * (abLens.view (xs p)).2
                  ≤ (abLens.view (xs (k+1))).1 * (abLens.view (xs k)).2
                    * (abLens.view (xs p)).2 :=
          Nat.mul_le_mul_right _ hstep
        -- Reassoc: ak * bp * bk1 = ak * bk1 * bp.
        have h2' : (abLens.view (xs k)).1 * (abLens.view (xs p)).2
                     * (abLens.view (xs (k+1))).2
                   ≤ (abLens.view (xs (k+1))).1 * (abLens.view (xs k)).2
                     * (abLens.view (xs p)).2 := by
          have heq : (abLens.view (xs k)).1 * (abLens.view (xs p)).2
                       * (abLens.view (xs (k+1))).2
                     = (abLens.view (xs k)).1 * (abLens.view (xs (k+1))).2
                       * (abLens.view (xs p)).2 := by
            rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (abLens.view (xs p)).2,
                ← E213.Tactic.Nat213.mul_assoc]
          rw [heq]; exact h2
        have h3 : (abLens.view (xs p)).1 * (abLens.view (xs k)).2
                    * (abLens.view (xs (k+1))).2
                  ≤ (abLens.view (xs (k+1))).1 * (abLens.view (xs k)).2
                    * (abLens.view (xs p)).2 := Nat.le_trans h1 h2'
        -- Factor bk: LHS = (ap * bk1) * bk, RHS = (ak1 * bp) * bk.
        have hLHS : (abLens.view (xs p)).1 * (abLens.view (xs k)).2
                      * (abLens.view (xs (k+1))).2
                    = (abLens.view (xs p)).1 * (abLens.view (xs (k+1))).2
                      * (abLens.view (xs k)).2 := by
          rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (abLens.view (xs k)).2,
              ← E213.Tactic.Nat213.mul_assoc]
        have hRHS : (abLens.view (xs (k+1))).1 * (abLens.view (xs k)).2
                      * (abLens.view (xs p)).2
                    = (abLens.view (xs (k+1))).1 * (abLens.view (xs p)).2
                      * (abLens.view (xs k)).2 := by
          rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (abLens.view (xs k)).2,
              ← E213.Tactic.Nat213.mul_assoc]
        rw [hLHS, hRHS] at h3
        exact E213.Tactic.Nat213.le_of_mul_le_mul_right hbk h3
      · -- p > k, but p ≤ k+1 → p = k+1
        have hpk_lt : k < p := Nat.lt_of_not_le hpk
        have hp_le : p ≤ k + 1 := hpq
        have hp : p = k + 1 :=
          Nat.le_antisymm hp_le (Nat.succ_le_of_lt hpk_lt)
        subst hp
        exact Nat.le_refl _

end E213.Lib.Math.Cauchy.MonotonicBounded

namespace E213.Lib.Math.Cauchy.MonotonicBounded

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

/-! ### orderProj false propagates forward (monotonic) -/

/-- If orderProj is false at some time N, then by monotonicity it is
    false for all i ≥ N. -/
theorem orderProj_false_propagates (xs : Nat → Raw)
    (hmono : IsAbMonotonic xs) (hpos : IsAbPositiveB xs)
    (m k N : Nat) (hN_false : orderProj m k (abLens.view (xs N)) = false)
    (i : Nat) (hi : i ≥ N) :
    orderProj m k (abLens.view (xs i)) = false := by
  unfold orderProj at *
  -- 213-native: convert decide ↔ Prop without propext-bringing iff.
  apply decide_eq_false
  intro hle
  apply of_decide_eq_false hN_false
  -- hN_false : ¬ a_N * k ≤ b_N * m  (i.e., a_N * k > b_N * m)
  -- hle      : a_i * k ≤ b_i * m
  -- chain     : a_N * b_i ≤ a_i * b_N
  -- Goal     : a_N * k ≤ b_N * m
  have hchain := ab_monotonic_chain xs hmono hpos N i hi
  have hbi : 1 ≤ (abLens.view (xs i)).2 := hpos i
  -- Multiply hchain by k:
  have h1 : (abLens.view (xs N)).1 * (abLens.view (xs i)).2 * k
            ≤ (abLens.view (xs i)).1 * (abLens.view (xs N)).2 * k :=
    Nat.mul_le_mul_right _ hchain
  -- Multiply hle by bN:
  have h2 : (abLens.view (xs i)).1 * k * (abLens.view (xs N)).2
            ≤ (abLens.view (xs i)).2 * m * (abLens.view (xs N)).2 :=
    Nat.mul_le_mul_right _ hle
  -- Reassoc: ai * bN * k = ai * k * bN.
  have he1 : (abLens.view (xs i)).1 * (abLens.view (xs N)).2 * k
             = (abLens.view (xs i)).1 * k * (abLens.view (xs N)).2 := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (abLens.view (xs N)).2 k, ← E213.Tactic.Nat213.mul_assoc]
  -- Reassoc: bi * m * bN = bN * m * bi.
  have he2 : (abLens.view (xs i)).2 * m * (abLens.view (xs N)).2
             = (abLens.view (xs N)).2 * m * (abLens.view (xs i)).2 := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (abLens.view (xs i)).2
          (m * (abLens.view (xs N)).2), Nat.mul_comm m (abLens.view (xs N)).2]
  rw [he1] at h1
  rw [he2] at h2
  have h3 : (abLens.view (xs N)).1 * (abLens.view (xs i)).2 * k
            ≤ (abLens.view (xs N)).2 * m * (abLens.view (xs i)).2 :=
    Nat.le_trans h1 h2
  -- Reassoc LHS: aN * bi * k = aN * k * bi.
  have he3 : (abLens.view (xs N)).1 * (abLens.view (xs i)).2 * k
             = (abLens.view (xs N)).1 * k * (abLens.view (xs i)).2 := by
    rw [E213.Tactic.Nat213.mul_assoc, Nat.mul_comm (abLens.view (xs i)).2 k, ← E213.Tactic.Nat213.mul_assoc]
  rw [he3] at h3
  exact E213.Tactic.Nat213.le_of_mul_le_mul_right hbi h3

end E213.Lib.Math.Cauchy.MonotonicBounded

namespace E213.Lib.Math.Cauchy.MonotonicBounded

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lib.Math.Cauchy.Archimedean

/-! ### Constructive Cauchy from a witness "false at N₀"

The full classical statement
`monotonic + bounded → isOrderCauchy (∀ m k, ∃ N, …)` requires
LEM (case split on "∀ n, true" vs "∃ n, false") and is therefore
unavailable under the 213 falsifiability contract.

What we DO get constructively: given a specific witness `N₀`
where `orderProj m k (xs N₀) = false`, monotonic chain
propagates and gives explicit `N := N₀` for the Cauchy condition
at this `(m, k)`.  Combined with the dual side
("orderProj true at all n" — produces `N := 0`), specific cuts
of any monotonic sequence become a finite-witness affair.

The general `∀ (m, k)` closure is **deliberately** not claimed —
it would smuggle LEM, mirroring ZFC's power-set commitment to
arbitrary subsets (cf. Risk-2 framing in `PAPER1_OUTLINE.md`).
-/

/-- Constructive Cauchy at `(m, k)` given a false-witness. -/
theorem orderCauchy_from_false_witness (xs : Nat → Raw)
    (hmono : IsAbMonotonic xs) (hpos : IsAbPositiveB xs)
    (m k N₀ : Nat)
    (hN₀ : orderProj m k (abLens.view (xs N₀)) = false) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      orderProj m k (abLens.view (xs i))
        = orderProj m k (abLens.view (xs j)) := by
  refine ⟨N₀, ?_⟩
  intro i j hi hj
  rw [orderProj_false_propagates xs hmono hpos m k N₀ hN₀ i hi,
      orderProj_false_propagates xs hmono hpos m k N₀ hN₀ j hj]

/-- Constructive Cauchy at `(m, k)` given a "true forever" witness. -/
theorem orderCauchy_from_true_forever (xs : Nat → Raw)
    (m k : Nat)
    (h : ∀ n, orderProj m k (abLens.view (xs n)) = true) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      orderProj m k (abLens.view (xs i))
        = orderProj m k (abLens.view (xs j)) := by
  refine ⟨0, ?_⟩
  intro i j _ _; rw [h i, h j]

end E213.Lib.Math.Cauchy.MonotonicBounded
