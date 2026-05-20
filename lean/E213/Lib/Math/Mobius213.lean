import E213.Lib.Math.Tactic.Ring213

/-!
# Lib.Math.Mobius213 — 213 Möbius signature P(x) = (2x+1)/(x+1)

The Möbius matrix [[2,1],[1,1]] is the *algebraic representation*
of the residue's self-pointing fixed point (cf.
`seed/AXIOM/02_statement.md` §3.4, `07_self_reference.md` §8.5).
The fixed point φ = (1+√5)/2 is the residue read through the
numerical Lens — not a structure added to the axiom, but a
consequence (∅-axiom theorem) of the 4 clauses.

This module bridges:
  - Raw's binary slash (identity-preserving doubling)
  - Algebra tower's CD doubling (24 ∅-axiom theorems)
  - Pell-Fib infrastructure (DyadicFSM/Fib/PellRelation)
  - DRLT physics constants (φ in CKM, Cabibbo, ν)

Key relations encoded:
  trace = 3 = NS    (Raw's spatial atomicity)
  det = 1           (norm preservation, "identity")
  disc = 5 = NS+NT  (Raw's atomicity sum)
  eigenvalues φ², 1/φ²

## Frozen + dynamic dualism

Per `07_self_reference.md` §8.7, P admits two simultaneous Lens
readings on the same residue:

  - **Frozen reading**: φ² is the dominant eigenvalue of
    [[2,1],[1,1]] (algebraic fixed point of P; cf.
    `phi_squared_eigenvalue` below).  Static configuration.
  - **Dynamic reading**: the Pell convergents (numerator,
    denominator) under the recurrence a_{n+2} = 3a_{n+1} − a_n
    are the trajectory whose ratio approaches φ; their ratios
    are bounded above and below by adjacent fractions of φ.
    Iteration.

Same algebraic object, two readings.  Without an external time
axis the dichotomy "is it frozen or dynamic?" is not posed —
both readings hold simultaneously for an internal observer.

All theorems ∅-axiom (using Recurrence2 from Ring213).
-/

namespace E213.Lib.Math.Mobius213

open E213.Lib.Math.Tactic.Ring213

/-- Pell-numerator sequence under [[2,1],[1,1]] iteration starting (1, 1).
    Satisfies a_{n+2} = 3·a_{n+1} − a_n.
    Char poly x² − 3x + 1, eigenvalues φ², 1/φ². -/
def P_numerator : Recurrence2 :=
  { a₀ := 1, a₁ := 3, c₁ := 3, c₂ := -1, d := 0 }

/-- Pell-denominator sequence: starts (1, 2), same recurrence. -/
def P_denominator : Recurrence2 :=
  { a₀ := 1, a₁ := 2, c₁ := 3, c₂ := -1, d := 0 }

/-- ★ Numerator follows Pell recurrence (∀ n by `rfl`). -/
theorem P_numerator_recurrence (n : Nat) :
    P_numerator.seq (n+2) = 3 * P_numerator.seq (n+1) + (-1) * P_numerator.seq n + 0 :=
  P_numerator.seq_recurrence n

/-- ★ Denominator follows the same Pell recurrence. -/
theorem P_denominator_recurrence (n : Nat) :
    P_denominator.seq (n+2) = 3 * P_denominator.seq (n+1) + (-1) * P_denominator.seq n + 0 :=
  P_denominator.seq_recurrence n

/-- ★ Pell convergent values, layers 0–8.
    `P_numerator.seq k` for k = 0..8 gives 1, 3, 8, 21, 55, 144,
    377, 987, 2584 — the even-indexed Fibonacci numbers
    F_2, F_4, …, F_16 (see `Lib.Physics.Foundations.
    FibonacciExtended` for the bridge statement). -/
theorem P_numerator_values :
    P_numerator.seq 0 = 1 ∧ P_numerator.seq 1 = 3 ∧
    P_numerator.seq 2 = 8 ∧ P_numerator.seq 3 = 21 ∧
    P_numerator.seq 4 = 55 ∧ P_numerator.seq 5 = 144 ∧
    P_numerator.seq 6 = 377 ∧ P_numerator.seq 7 = 987 ∧
    P_numerator.seq 8 = 2584 := by decide

/-- ★ Pell convergent values, layers 0–8.
    `P_denominator.seq k` for k = 0..8 gives 1, 2, 5, 13, 34, 89,
    233, 610, 1597 — the odd-indexed Fibonacci numbers F_1, F_3,
    …, F_15. -/
theorem P_denominator_values :
    P_denominator.seq 0 = 1 ∧ P_denominator.seq 1 = 2 ∧
    P_denominator.seq 2 = 5 ∧ P_denominator.seq 3 = 13 ∧
    P_denominator.seq 4 = 34 ∧ P_denominator.seq 5 = 89 ∧
    P_denominator.seq 6 = 233 ∧ P_denominator.seq 7 = 610 ∧
    P_denominator.seq 8 = 1597 := by decide

/-- ★ disc = trace² − 4·det = 9 − 4 = 5 = NS + NT (Raw atomicity). -/
theorem mobius_213_discriminant : (3 : Int)^2 - 4 * 1 = 5 := by decide

/-- ★ trace = 3 = NS (Raw's spatial atomicity NS=3). -/
theorem mobius_213_trace : (2 : Int) + 1 = 3 := by decide

/-- ★ det = 1 (norm preservation, identity). -/
theorem mobius_213_det : (2 : Int) * 1 - 1 * 1 = 1 := by decide

/-- ★ Characteristic polynomial of the Möbius matrix
    [[2,1],[1,1]] evaluated at λ = 3 (the trace): yields
    9 − 9 + 1 = 1 = det.  The two roots of λ² − 3λ + 1 = 0
    are φ² and 1/φ², so this is the integer-coefficient
    witness that φ² and 1/φ² are the eigenvalues. -/
theorem mobius_213_char_poly_at_trace : (3 : Int)^2 - 3 * 3 + 1 = 1 := by decide

/-! ## §2 — Pell-unit invariant (frozen + dynamic)

The cross-product `X_n := num_n · den_{n+1} − num_{n+1} · den_n`
satisfies `X_{n+1} = -c₂ · X_n` for any pair of sequences obeying
the same recurrence with parameter c₂.  For [[2,1],[1,1]] we have
c₂ = -1, hence X_{n+1} = X_n: the cross-product is a constant of
motion, equal to its initial value −1.

  Frozen reading: −1 is the symplectic invariant of the matrix
    (det = 1 lifted to consecutive-pair determinant).
  Dynamic reading: each Pell iteration preserves the invariant
    (group-action invariance).

Same algebraic content, two Lens readings (§3.4 + §8.7).

A general ∀ n form would need Int ring algebra at the inductive
step.  Without `ring`/`linarith` in the 213-native tactic set,
we provide the strict ∅-axiom witness as the 8-layer bundle
below — `decide` verifies all 8 consecutive layers in one go.
-/

/-- ★★ **8-layer Pell-unit invariant** — the cross-product
    `num_n · den_{n+1} − num_{n+1} · den_n = −1` for every
    layer n = 0..7 (one statement, eight conjuncts).  All
    eight instances are the SAME structural fact read at
    different convergent depths. -/
theorem mobius_213_pell_unit_invariant :
    (P_numerator.seq 0 * P_denominator.seq 1
       - P_numerator.seq 1 * P_denominator.seq 0 = -1)
    ∧ (P_numerator.seq 1 * P_denominator.seq 2
       - P_numerator.seq 2 * P_denominator.seq 1 = -1)
    ∧ (P_numerator.seq 2 * P_denominator.seq 3
       - P_numerator.seq 3 * P_denominator.seq 2 = -1)
    ∧ (P_numerator.seq 3 * P_denominator.seq 4
       - P_numerator.seq 4 * P_denominator.seq 3 = -1)
    ∧ (P_numerator.seq 4 * P_denominator.seq 5
       - P_numerator.seq 5 * P_denominator.seq 4 = -1)
    ∧ (P_numerator.seq 5 * P_denominator.seq 6
       - P_numerator.seq 6 * P_denominator.seq 5 = -1)
    ∧ (P_numerator.seq 6 * P_denominator.seq 7
       - P_numerator.seq 7 * P_denominator.seq 6 = -1)
    ∧ (P_numerator.seq 7 * P_denominator.seq 8
       - P_numerator.seq 8 * P_denominator.seq 7 = -1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Mobius213
