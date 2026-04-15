/-
  YangMills/ChebyshevAction.lean

  The algebraic action: arccos eliminated via Chebyshev polynomials.

  KEY IDENTITY (Mathlib):
    T_n(cos θ) = cos(nθ)    — Chebyshev polynomial = integer-coeff polynomial

  ALGEBRAIC ACTION:
    S[G] = Σ_h √det(G_h) · Σ_n (1 - T_n(cos θ_h)) / n²

  where:
    - cos θ_h = algebraic function of Gram matrix entries
    - T_n = integer-coefficient polynomial (Chebyshev)
    - 1/n² = integer reciprocal squares
    - π appears ONLY as ζ(2) = Σ 1/n² = π²/6

  Everything is number-theoretic. No arccos anywhere.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.NumberTheory.ZetaValues
import YangMills.MassGap

set_option autoImplicit false

open Polynomial.Chebyshev Polynomial Real

namespace DRLT.YangMills

/-! ## 1. Chebyshev T_n Is an Integer-Coefficient Polynomial

  T_n ∈ ℤ[x]: the Chebyshev polynomial of the first kind has
  integer coefficients.  This is the algebraicity that replaces
  the transcendental arccos.
-/

/-- T_n(cos θ) = cos(nθ) — the fundamental Chebyshev identity.
    This is Mathlib's `Polynomial.Chebyshev.T_real_cos`.
    We re-export it with a cleaner name. -/
theorem chebyshev_cos (n : ℤ) (theta : ℝ) :
    (T ℝ n).eval (cos theta) = cos (↑n * theta) :=
  T_real_cos theta n

/-! ## 2. The Algebraic Summand

  The quantity (1 - T_n(x)) / n² is the algebraic replacement
  for the deficit angle.  When x = cos θ:
    (1 - T_n(cos θ)) / n² = (1 - cos(nθ)) / n²

  Summing over n → ∞ gives a series related to θ² and ζ(2).
-/

/-- The n-th algebraic summand: (1 - T_n(x)) / n² -/
noncomputable def algebraicSummand (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (1 - (T ℝ (n : ℤ)).eval x) / (n : ℝ) ^ 2

/-- For x = cos θ, the summand becomes (1 - cos(nθ)) / n² -/
theorem algebraicSummand_eq_cos (theta : ℝ) (n : ℕ) (hn : n ≠ 0) :
    algebraicSummand (cos theta) n = (1 - cos (↑n * theta)) / (↑n) ^ 2 := by
  unfold algebraicSummand
  simp [hn, chebyshev_cos]

/-! ## 3. Connection to ζ(2) = π²/6

  Σ_{n=1}^∞ 1/n² = π²/6 (Basel problem / ζ(2))

  At θ = 0: cos(nθ) = 1, so each summand = 0.
  At θ = π: cos(nπ) = (-1)^n, and the series relates to π².
-/

/-- At x = 1 (θ = 0), all summands vanish: flat space has no curvature.
    T_n(1) = 1 for all n, so 1 - T_n(1) = 0. -/
theorem algebraicSummand_at_one (n : ℕ) :
    algebraicSummand 1 n = 0 := by
  unfold algebraicSummand
  split
  · rfl
  · next h =>
    rw [show (1 : ℝ) = cos 0 from (cos_zero).symm, chebyshev_cos]
    simp

/-! ## 4. The Mass Gap via ζ(2)

  Δ = √det · π = √det · √(6ζ(2)) = √det · √(6 · Σ 1/n²)

  This replaces the "transcendental" mass gap formula with a
  purely number-theoretic one.
-/

/-- THE BASEL PROBLEM (Mathlib):
    Σ_{n=0}^∞ 1/n² = π²/6.
    This is ζ(2) = π²/6, proved by Euler (1734).
    We re-export Mathlib's `hasSum_zeta_two`. -/
theorem basel : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two

/-- π² = 6 · ζ(2) = 6 · (Σ 1/n²).
    This is the Basel problem rearranged: π² is 6 times the
    sum of integer reciprocal squares. -/
theorem pi_sq_eq_six_tsum :
    Real.pi ^ 2 = 6 * ∑' (n : ℕ), (1 : ℝ) / (n : ℝ) ^ 2 := by
  have h := hasSum_zeta_two.tsum_eq
  linarith

/-- Δ² = det · π² -/
theorem mass_gap_sq_eq (g : GramAAA) :
    (massGap g) ^ 2 = g.det * Real.pi ^ 2 := by
  unfold massGap reggeAction hingeArea
  rw [mul_pow, Real.sq_sqrt (le_of_lt g.det_pos)]

/-- THE MASS GAP IS A PRODUCT OF INTEGERS (via Basel):
    Δ² = det · 6 · (Σ_{n=0}^∞ 1/n²)

    - det: algebraic (from Gram matrix of ℂ³ vectors)
    - 6: integer
    - Σ 1/n²: sum of integer reciprocal squares (= ζ(2))

    π appears NOWHERE explicitly. It is the VALUE of the
    integer series, not an INPUT to the theory. -/
theorem mass_gap_sq_eq_zeta (g : GramAAA) :
    (massGap g) ^ 2 = g.det * (6 * ∑' (n : ℕ), (1 : ℝ) / (n : ℝ) ^ 2) := by
  rw [mass_gap_sq_eq, pi_sq_eq_six_tsum]

/-- Δ² > 0 (follows from det > 0 and π² > 0) -/
theorem mass_gap_sq_pos (g : GramAAA) :
    0 < (massGap g) ^ 2 := by
  rw [mass_gap_sq_eq]
  exact mul_pos g.det_pos (pow_pos Real.pi_pos 2)

/-! ## 5. The Chebyshev Expansion Connects Algebra to Geometry

  The deficit angle δ = π at the AAA hinge means:
    cos(δ) = cos(π) = -1

  T_n(cos θ₁) where θ₁ = π/2 (the first dihedral angle):
    T_n(0) = cos(nπ/2) ∈ {1, 0, -1, 0, ...}

  This is a PURELY ALGEBRAIC sequence (it's periodic in n mod 4).
  The "transcendental" cos(nπ/2) is actually algebraic when
  evaluated at rational multiples of π.
-/

/-- T_n(0) = cos(nπ/2): evaluating Chebyshev at 0 gives
    the periodic sequence {1, 0, -1, 0, ...} -/
theorem chebyshev_at_zero (n : ℤ) :
    (T ℝ n).eval 0 = cos (↑n * (Real.pi / 2)) := by
  rw [show (0 : ℝ) = cos (Real.pi / 2) from (cos_pi_div_two).symm]
  exact chebyshev_cos n (Real.pi / 2)

/-- At x = -1 (θ = π, i.e. deficit angle δ = π):
    T_n(-1) = cos(nπ).  This is the Chebyshev evaluation at the
    deficit angle of the AAA hinge. -/
theorem chebyshev_at_deficit (n : ℤ) :
    (T ℝ n).eval (-1) = cos (↑n * Real.pi) := by
  rw [show (-1 : ℝ) = cos Real.pi from (cos_pi).symm]
  exact chebyshev_cos n Real.pi

end DRLT.YangMills
