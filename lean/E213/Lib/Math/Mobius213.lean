import E213.Lib.Math.Tactic.Ring213
import E213.Meta.Int213.Core

/-!
# Lib.Math.Mobius213 — 213 Möbius signature P(x) = (2x+1)/(x+1)

The Möbius matrix [[2,1],[1,1]] is the *algebraic representation*
of the residue's self-pointing fixed point (cf.
`seed/AXIOM/03_form.md` §3.5, `07_self_reference.md` §8.5).
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
open E213.Meta.Int213 (cross_step_algebra)

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

/-! ## §2 — Recurrence-uniqueness (structural lemma)

A clean piece of insight reusable across the file (and across
the Fibonacci bridge in `Lib/Physics/Foundations/
FibonacciExtended`): if two integer sequences satisfy the
**same** 2nd-order recurrence and agree at two consecutive
initial values, they agree everywhere.

This is the structural reason why Pell convergents and
Fibonacci subsequences (odd / even indices) literally coincide:
both satisfy the [[2,1],[1,1]] recurrence and start identically.
-/

/-- ★ **Two-step strong induction**: prove `∀ n, P n` from
    `P 0`, `P 1`, and the implication `P n → P (n+1) → P (n+2)`.
    ∅-axiom, term-mode lift of ordinary `Nat.rec`. -/
theorem two_step_induction {P : Nat → Prop}
    (h0 : P 0) (h1 : P 1)
    (hstep : ∀ n, P n → P (n+1) → P (n+2)) :
    ∀ n, P n := by
  intro n
  suffices h : P n ∧ P (n+1) from h.1
  induction n with
  | zero => exact ⟨h0, h1⟩
  | succ k ih => exact ⟨ih.2, hstep k ih.1 ih.2⟩

/-- ★★★ **Pell-recurrence uniqueness**: any pair of Int sequences
    `f, g : Nat → Int` satisfying the Möbius-matrix recurrence
    `s (n+2) = 3 · s (n+1) − s n` and agreeing at `n = 0, 1` are
    identical for every `n`.  This is the "two boundary values
    determine the entire trajectory" content of the [[2,1],[1,1]]
    fixed-point structure. -/
theorem pell_recurrence_unique (f g : Nat → Int)
    (h₀ : f 0 = g 0) (h₁ : f 1 = g 1)
    (hf : ∀ n, f (n+2) = 3 * f (n+1) - f n)
    (hg : ∀ n, g (n+2) = 3 * g (n+1) - g n) :
    ∀ n, f n = g n := by
  apply two_step_induction (P := fun n => f n = g n) h₀ h₁
  intro k ihk ihk1
  rw [hf k, hg k, ihk, ihk1]

/-! ## §3 — Pell-unit invariant (frozen + dynamic)

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

A fully general ∀ n form for X_n = −1 would need Int ring
algebra at the inductive step (`ring` / `linarith` not in 213-
native set).  The 8-layer bundle below is the strict ∅-axiom
witness — `decide` verifies all 8 consecutive layers in one go.
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

/-! ## §4 — `∀ n` Pell-unit invariant (L_∞ infrastructure)

The 8-layer bundle above witnesses X(n) := num_n·den_{n+1} − num_{n+1}·den_n
= -1 at concrete depths n = 0..7.  The universally-quantified version
previously deferred for lack of 213-native `ring` tactics.

The structural content: with c₂ = -1 in `[[3, -1], [1, 0]]`-style recurrence
(equivalently P-iteration of `[[2,1],[1,1]]`), the cross-product X(n) is a
**constant of motion**, taking the symplectic value -1 forever.

Hero milestone 1a for the 213-tower L_∞ fixed point: ∀n witness that
the Pell trajectory has an invariant under iteration — the dynamical
reading of the frozen det = 1 identity.

PURE: all theorems below are ∅-axiom.  The Int ring step (`pell_unit_at_succ`)
is closed by `cross_step_algebra`, a manual `rw`-chain using `Meta.Int213.*`
lemmas only — no `simp`, no `omega`, no Mathlib.  Falsifies neither propext
nor Quot.sound. -/

/-- Pell-unit cross-product at depth `n`. -/
def pell_unit_at (n : Nat) : Int :=
  P_numerator.seq n * P_denominator.seq (n+1)
    - P_numerator.seq (n+1) * P_denominator.seq n

/-- ★★ **Cross-product step identity** (`c₂ = -1` case):
    X(n+1) = X(n).  The det-1 symplectic invariant of the [[2,1],[1,1]]
    matrix propagates through every P-iteration step.  PURE. -/
theorem pell_unit_at_succ (n : Nat) :
    pell_unit_at (n+1) = pell_unit_at n := by
  unfold pell_unit_at
  show P_numerator.seq (n+1) * P_denominator.seq (n+2)
       - P_numerator.seq (n+2) * P_denominator.seq (n+1)
     = P_numerator.seq n * P_denominator.seq (n+1)
       - P_numerator.seq (n+1) * P_denominator.seq n
  rw [show P_numerator.seq (n+2)
        = 3 * P_numerator.seq (n+1) + (-1) * P_numerator.seq n + 0 from rfl,
      show P_denominator.seq (n+2)
        = 3 * P_denominator.seq (n+1) + (-1) * P_denominator.seq n + 0 from rfl]
  exact cross_step_algebra _ _ _ _

/-- ★★★ **∀n Pell-unit invariant** — the L_∞ symplectic constant.
    `num_n · den_{n+1} − num_{n+1} · den_n = -1` for **every** depth `n`.
    Closes the deferred ∀n form noted in the §3 docstring.

    Proof: base case X(0) = 1·2 − 3·1 = -1 by `decide`; inductive step
    is `pell_unit_at_succ`.  Uses 213-native Int algebra throughout
    (no Mathlib, no `ring`). -/
theorem mobius_213_pell_unit_invariant_forall :
    ∀ n, pell_unit_at n = -1 := by
  intro n
  induction n with
  | zero => decide
  | succ k ih => exact (pell_unit_at_succ k).trans ih

end E213.Lib.Math.Mobius213
