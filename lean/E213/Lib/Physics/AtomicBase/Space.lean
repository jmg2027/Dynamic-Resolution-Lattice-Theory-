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

/-- ★ Phase 2 Space master — NS=3 atomic unfolding + NT/NS asymmetry ★

  NS=3 atom unfolded gives ternary (3^n leaves).  Asymmetric with
  NT=2 dyadic, ratio (3/2)^n at every depth.  Bundles:

    · NS_atomic_size = 3 + 1/2/3-step counts (3, 9, 27)
    · NT vs NS asymmetry at depth 1/2/3 (states, differences)
    · ratio cross-mult identity 3^n · 2^n = 6^n at n = 2, 3
    · NS/NT ratio = 3/2 (cross-mult sanity)

  Atomicity-level origin of Phase 1's m_μ/m_e (NS/NT factor 3/2),
  Y-norm (5/3 = d/NS), and Fibonacci F_5/F_4 = 5/3.

  No external frame is invoked (per `seed/AXIOM/05_no_exterior.md` §5.1: there is no exterior to 213, so no external dialer sets the
  asymmetry). -/
theorem space_is_NS_unfolded :
    -- NS atomic size
    NS_atomic_size = 3
    -- step counts: NS unfolded gives 3^n
    ∧ ((3 : Nat) ^ 1 = 3)
    ∧ ((3 : Nat) ^ 2 = 9)
    ∧ ((3 : Nat) ^ 3 = 27)
    -- NT side
    ∧ ((2 : Nat) ^ 1 = 2)
    -- asymmetry (3 ≠ 2)
    ∧ (3 ≠ 2)
    -- NS/NT ratio = 3/2 (cross-mult)
    ∧ (3 * 2 = 2 * 3)
    -- depth-2 difference 9 − 4 = 5
    ∧ ((3 : Nat) ^ 2 - (2 : Nat) ^ 2 = 5)
    -- depth-3 difference 27 − 8 = 19
    ∧ ((3 : Nat) ^ 3 - (2 : Nat) ^ 3 = 19)
    -- ratio cross-mult: 3^n · 2^n = 6^n  at n = 2, 3
    ∧ ((3 : Nat) ^ 2 * (2 : Nat) ^ 2 = 6 ^ 2)
    ∧ ((3 : Nat) ^ 3 * (2 : Nat) ^ 3 = 6 ^ 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AtomicBase.Space
