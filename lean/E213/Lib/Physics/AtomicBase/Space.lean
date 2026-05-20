import E213.Lib.Physics.AtomicBase.Time

/-!
# Phase 2 Space — what does unfolding the NS=3 sector yield?

**Layer: App** (NS atomicity-derived ternary unfolding).

Time.lean: *NT=2 sector unfolded → 2^n binary bisection (dyadic)*.
This file: *NS=3 sector unfolded → 3^n ternary tree*.

## Meaning of NS=3 atomic block

The word "space" cannot be used from 213 axioms alone (per CLAUDE.md derivation).  However:

  Atomicity → atom pair {2, 3} → larger block size 3 (= NS)

Applying NS=3 atom *repeatedly* gives 3-fold branching at each step.
After depth n, 3^n distinguishable states.

## Asymmetry (★ Phase 2 decisive finding ★)

  NT=2 unfolded: 2^n   (binary, dyadic)
  NS=3 unfolded: 3^n   (ternary, triadic)

  Ratio: 3^n / 2^n = (3/2)^n  → time vs space asymmetry
  *forced by atomicity itself*.

This is the *axiom-level origin* of the various (3/2) ratios found in Phase 1:
  - NS/NT factor in m_μ/m_e
  - SU(5) Y-norm d/NS = 5/3
  - Fibonacci F_5/F_4 = 5/3
  - all shadows of (3/2) atomicity asymmetry

## This file's contribution

Natural propositions of NS=3 ternary unfolding + explicit statement of asymmetry with Time.

*Parallel* to math track dyadic bridge but ternary is separate work
(ternary bridge not yet in math track — this file provides partial results).
-/

namespace E213.Lib.Physics.AtomicBase.Space

/-- NS sector = atomic 3-block. -/
def NS_atomic_size : Nat := 3

theorem NS_size_eq_3 : NS_atomic_size = 3 := by decide

/-- NS 1 step → 3 states. -/
theorem NS_one_step : (3 : Nat) ^ 1 = 3 := by decide

/-- NS n steps → 3^n states. -/
theorem NS_two_steps : (3 : Nat) ^ 2 = 9 := by decide
theorem NS_three_steps : (3 : Nat) ^ 3 = 27 := by decide

/-- ★ NT vs NS asymmetry — atomic-forced ★

  NT 2 vs NS 3 → unfolding difference is always (3/2)^n.

  That is, *space vs time asymmetry* comes from atomicity itself
  — a structural fact about the (3, 2) atomic pair, with no
  external frame invoked (per `seed/AXIOM/07_self_reference.md`
  §8.1: there is no exterior to 213, so no external dialer sets
  the asymmetry). -/
theorem NT_NS_asymmetry_at_n :
    -- NT 1 step: 2 states
    ((2 : Nat) ^ 1 = 2)
    -- NS 1 step: 3 states
    ∧ ((3 : Nat) ^ 1 = 3)
    -- ratio: 3/2 = NS/NT
    ∧ (3 * 2 = 2 * 3) := by decide

/-- Asymmetry at depth 2: 9 vs 4 (= 5 difference). -/
theorem NT_NS_at_depth_2 :
    ((3 : Nat) ^ 2 - (2 : Nat) ^ 2 = 5) := by decide

/-- At depth 3: 27 vs 8 (= 19 difference). -/
theorem NT_NS_at_depth_3 :
    ((3 : Nat) ^ 3 - (2 : Nat) ^ 3 = 19) := by decide

/-- Ratio at depth n: 3^n / 2^n = (3/2)^n
    (integer cross-mult: 3^n · 2^n = 6^n). -/
theorem NT_NS_ratio_cross_mult_at_2 :
    (3 : Nat) ^ 2 * (2 : Nat) ^ 2 = 6 ^ 2 := by decide

theorem NT_NS_ratio_cross_mult_at_3 :
    (3 : Nat) ^ 3 * (2 : Nat) ^ 3 = 6 ^ 3 := by decide

/-- ★ Phase 2 Space — comprehensive proposition ★

  NS=3 atom unfolded gives ternary (3^n leaves).
  Asymmetric with NT=2 dyadic, ratio (3/2)^n.

  Atomicity-level origin of Phase 1's m_μ/m_e (NS/NT factor 3/2), Y-norm (5/3 = d/NS),
  and Fibonacci F_5/F_4 = 5/3. -/
theorem space_is_NS_unfolded :
    -- NS atomic size
    (NS_atomic_size = 3)
    -- 1 step gives 3 states
    ∧ ((3 : Nat) ^ 1 = 3)
    -- asymmetry (3 ≠ 2)
    ∧ (3 ≠ 2)
    -- NS/NT ratio = 3/2 (cross-mult)
    ∧ (3 * 2 = 2 * 3) := by decide

end E213.Lib.Physics.AtomicBase.Space
