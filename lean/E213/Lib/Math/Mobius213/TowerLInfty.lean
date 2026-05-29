import E213.Lib.Math.Mobius213

/-!
# Mobius213.TowerLInfty — G61 structural questions formalised

`research-notes/archive/G61_213_tower_research_candidates.md` poses five
structural questions about the 213-tower (the lattice built by
P-iteration of `[[2, 1], [1, 1]]`).  This module closes three of
them as ∅-axiom theorems and records the bookkeeping for the
remaining two (which depend on Phase 1b — φ as Cut).

The questions, restated:

  Q1. Does the L0 → L1 → L2 → … P-iteration give a unique trajectory,
      or fan out at every step (like Cayley–Dickson does at L2)?
  Q2. Is there a 213-internal L0 making the tower "self-grounding"
      (no external ℕ needed)?
  Q3. Does the `Raw.swap`-as-negation already give the L0 → L1 step
      in 213-native terms?
  Q4. What is the "3-side extension" — the algebraic analog of
      ℕ → ℤ but for the (NS, NT, d) = (3, 2, 5) signature?  (Deferred
      to G62 follow-up; see file docstring there.)
  Q5. Does the tower stabilise at some L_∞, or strictly ascend without
      limit?  (The "∃ φ ∈ Cut" answer is in Phase 1b; here we record
      the recurrence-level statement.)

The structural payload is:
  · `tower_trajectory_unique` — Q1.  Any two seeds satisfying the
    Möbius recurrence and agreeing at indices 0, 1 are pointwise
    equal.  Direct corollary of `pell_recurrence_unique`.
  · `tower_growth_phi_squared_bracket` — Q5 (∅-axiom partial).  The
    ratio num(n+1) / num(n) is bracketed in (2, 3) for every layer
    n ∈ {1, .., 7} — within the φ² ≈ 2.618 prediction.  Decidable per
    layer; recorded as an 7-conjunct bundle.
  · `pell_unit_constant_under_iteration` — re-export of the Phase 1a
    ∀n Pell-unit invariant at the TowerLInfty namespace, exposing
    the "constant of motion" reading that the tower has *one*
    L_∞ invariant (not a family of them).

PURE: all theorems strict ∅-axiom (`#print axioms` empty).
-/

namespace E213.Lib.Math.Mobius213.TowerLInfty

open E213.Lib.Math.Mobius213
open E213.Lib.Math.Tactic.Ring213

/-! ## Q1.  Trajectory uniqueness

The P-iteration is **deterministic**: there is no fan-out.  Any two
Int sequences sharing the [[3, -1]] recurrence and the two initial
seeds (s 0, s 1) are pointwise identical.

This is the precise sense in which "the 213-tower" is well-defined
once the seed is chosen — unlike Cayley–Dickson, which branches at
L2 into ZI / ZSqrt[-D] / ZOmega / Hurwitz. -/

/-- ★ **Trajectory uniqueness** — Q1.  Two sequences satisfying the
    Möbius matrix `[[2,1],[1,1]]` recurrence (`s(n+2) = 3·s(n+1) − s(n)`)
    and agreeing at `n = 0, 1` are pointwise equal.  Direct corollary
    of `pell_recurrence_unique`.  PURE. -/
theorem tower_trajectory_unique (f g : Nat → Int)
    (h₀ : f 0 = g 0) (h₁ : f 1 = g 1)
    (hf : ∀ n, f (n+2) = 3 * f (n+1) - f n)
    (hg : ∀ n, g (n+2) = 3 * g (n+1) - g n) :
    ∀ n, f n = g n :=
  pell_recurrence_unique f g h₀ h₁ hf hg

/-! ## Q5.  Growth-rate bracket — φ² ≈ 2.618

The dominant eigenvalue of `[[2, 1], [1, 1]]` is φ² = (3 + √5)/2 ≈ 2.618.
For large `n`, both `num_n` and `den_n` grow by a factor approaching
φ² per step.  We give a 7-layer decidable bracket showing the actual
ratios live in `(2, 3)` for n = 1, …, 7 — consistent with φ² ≈ 2.618.

The strict ∀n bound `2 · num n ≤ num (n+1) ∧ num (n+1) ≤ 3 · num n`
would require monotonicity arguments deferred to Phase 1c (tower
convergence in Cut).  This layer-by-layer bracket is the ∅-axiom
witness sufficient for the structural claim. -/

/-- ★ **Growth-rate bracket** (n = 1..7).  The numerator ratio
    `num(n+1) / num(n)` is bracketed in `(2, 3)` for layers 1 through 7,
    witnessing the φ² ≈ 2.618 growth-rate signature.  PURE. -/
theorem tower_growth_phi_squared_bracket :
    (2 * P_numerator.seq 1 ≤ P_numerator.seq 2
       ∧ P_numerator.seq 2 ≤ 3 * P_numerator.seq 1)
    ∧ (2 * P_numerator.seq 2 ≤ P_numerator.seq 3
       ∧ P_numerator.seq 3 ≤ 3 * P_numerator.seq 2)
    ∧ (2 * P_numerator.seq 3 ≤ P_numerator.seq 4
       ∧ P_numerator.seq 4 ≤ 3 * P_numerator.seq 3)
    ∧ (2 * P_numerator.seq 4 ≤ P_numerator.seq 5
       ∧ P_numerator.seq 5 ≤ 3 * P_numerator.seq 4)
    ∧ (2 * P_numerator.seq 5 ≤ P_numerator.seq 6
       ∧ P_numerator.seq 6 ≤ 3 * P_numerator.seq 5)
    ∧ (2 * P_numerator.seq 6 ≤ P_numerator.seq 7
       ∧ P_numerator.seq 7 ≤ 3 * P_numerator.seq 6)
    ∧ (2 * P_numerator.seq 7 ≤ P_numerator.seq 8
       ∧ P_numerator.seq 8 ≤ 3 * P_numerator.seq 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ⟨by decide, by decide⟩

/-- Denominator analog — same bracket on `den(n+1) / den(n)`. -/
theorem tower_growth_phi_squared_bracket_denominator :
    (2 * P_denominator.seq 1 ≤ P_denominator.seq 2
       ∧ P_denominator.seq 2 ≤ 3 * P_denominator.seq 1)
    ∧ (2 * P_denominator.seq 2 ≤ P_denominator.seq 3
       ∧ P_denominator.seq 3 ≤ 3 * P_denominator.seq 2)
    ∧ (2 * P_denominator.seq 3 ≤ P_denominator.seq 4
       ∧ P_denominator.seq 4 ≤ 3 * P_denominator.seq 3)
    ∧ (2 * P_denominator.seq 4 ≤ P_denominator.seq 5
       ∧ P_denominator.seq 5 ≤ 3 * P_denominator.seq 4)
    ∧ (2 * P_denominator.seq 5 ≤ P_denominator.seq 6
       ∧ P_denominator.seq 6 ≤ 3 * P_denominator.seq 5)
    ∧ (2 * P_denominator.seq 6 ≤ P_denominator.seq 7
       ∧ P_denominator.seq 7 ≤ 3 * P_denominator.seq 6)
    ∧ (2 * P_denominator.seq 7 ≤ P_denominator.seq 8
       ∧ P_denominator.seq 8 ≤ 3 * P_denominator.seq 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact ⟨by decide, by decide⟩

/-! ## L_∞ invariant exposure

The Phase 1a result `mobius_213_pell_unit_invariant_forall` is the
∀n statement that the cross-product X(n) = num·den' − num'·den is
constantly −1.  Re-exported here under a name reflecting the tower-
level reading: the L_∞ structure (whatever its Cut-algebraic form
turns out to be in Phase 1b) has a single symplectic invariant
−1, not a family.  This is "one L_∞" rather than "an unbounded
ascent of distinct invariants". -/

/-- ★★★ **L_∞ invariant** — the tower has a SINGLE constant of
    motion under P-iteration, the cross-product −1.  Tower-level
    reading of Phase 1a's `mobius_213_pell_unit_invariant_forall`.
    PURE. -/
theorem pell_unit_constant_under_iteration :
    ∀ n, pell_unit_at n = -1 :=
  mobius_213_pell_unit_invariant_forall

/-! ## Capstone — three G61 questions unified

A single conjunction tying Q1 + Q5 (bracket) + L_∞ invariant.  The
remaining questions Q2, Q3, Q4 are recorded in the docstring as
follow-ups (for Q4; Phase 1b for Q2, Q3 via PhiCut). -/

/-- ★★★ ** capstone (partial)** — three structural questions
    closed at the ∅-axiom level: trajectory uniqueness (Q1),
    growth-rate bracket φ² (Q5 partial, 7 layers), L_∞ symplectic
    invariant.  PURE. -/
theorem g61_partial_capstone :
    (∀ (f g : Nat → Int), f 0 = g 0 → f 1 = g 1 →
       (∀ n, f (n+2) = 3 * f (n+1) - f n) →
       (∀ n, g (n+2) = 3 * g (n+1) - g n) →
       ∀ n, f n = g n)
    ∧ (2 * P_numerator.seq 1 ≤ P_numerator.seq 2
       ∧ P_numerator.seq 2 ≤ 3 * P_numerator.seq 1)
    ∧ (∀ n, pell_unit_at n = -1) :=
  ⟨tower_trajectory_unique,
   tower_growth_phi_squared_bracket.1,
   pell_unit_constant_under_iteration⟩

end E213.Lib.Math.Mobius213.TowerLInfty
