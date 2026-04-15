/-
  YangMills/Hadamard.lean

  Hadamard-type inequalities and mass gap bounds.

  1. AM-GM: x² + y² ≥ 2xy (key for 3×3 Hadamard)
  2. The 3×3 algebraic core: a²+b²+c² ≥ 2abc
  3. Mass gap interval: 0 < Δ ≤ π
  4. Hinge area bound: 0 < A ≤ 1

  Philosophy (정수론/대수학 → 해석학):
  The Hadamard bound is the algebraic statement that unit vectors
  span at most unit volume. The continuum limit turns this into
  an analytic constraint; here it's a finite combinatorial fact.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/

import YangMills.MassGap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DRLT.YangMills

/-! ## 1. AM-GM and the Core Algebraic Inequality -/

/-- AM-GM for two squares: x² + y² ≥ 2xy.
    Proof: (x - y)² ≥ 0. -/
theorem two_mul_le_sq_add_sq (x y : ℝ) :
    2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]

/-- The core algebraic inequality for the 3×3 Hadamard bound:
    a² + b² + c² ≥ 2abc when c ∈ [0, 1].

    Proof: AM-GM gives a²+b² ≥ 2ab. Since c ≤ 1, 2ab ≥ 2abc.
    Adding c² ≥ 0 gives the result. -/
theorem sq_sum_ge_two_prod (a b c : ℝ)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    2 * a * b * c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : 2 * a * b ≤ a ^ 2 + b ^ 2 := two_mul_le_sq_add_sq a b
  nlinarith [sq_nonneg c, mul_nonneg _ha _hb]

/-- Symmetric version: also holds for permutations -/
theorem sq_sum_ge_two_prod' (a b c : ℝ)
    (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) (hb0 : 0 ≤ b) (_hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    2 * a * b * c ≤ a ^ 2 + b ^ 2 + c ^ 2 :=
  sq_sum_ge_two_prod a b c ha0 hb0 hc0 hc1

/-! ## 2. Hinge Area Bounds -/

/-- The hinge area A = √det is in (0, 1] for any GramAAA. -/
theorem hingeArea_le_one (g : GramAAA) :
    hingeArea g ≤ 1 := by
  unfold hingeArea
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt g.det_le_one

/-- The hinge area is positive -/
theorem hingeArea_pos' (g : GramAAA) :
    0 < hingeArea g := hingeArea_pos g

/-- The hinge area is in the interval (0, 1] -/
theorem hingeArea_in_interval (g : GramAAA) :
    0 < hingeArea g ∧ hingeArea g ≤ 1 :=
  ⟨hingeArea_pos g, hingeArea_le_one g⟩

/-! ## 3. Mass Gap Bounds -/

/-- The mass gap is bounded above: Δ ≤ π.
    Since A ≤ 1 and δ = π, we get Δ = A·π ≤ π. -/
theorem mass_gap_le_pi (g : GramAAA) :
    massGap g ≤ Real.pi := by
  unfold massGap reggeAction
  exact mul_le_of_le_one_left (le_of_lt Real.pi_pos) (hingeArea_le_one g)

/-- THE MASS GAP INTERVAL: 0 < Δ ≤ π.
    The mass gap is bounded away from zero and bounded
    above by π (Planck units). -/
theorem mass_gap_in_interval (g : GramAAA) :
    0 < massGap g ∧ massGap g ≤ Real.pi :=
  ⟨mass_gap_pos g, mass_gap_le_pi g⟩

/-- For the ideal simplex, Δ = π exactly (saturates the bound) -/
theorem mass_gap_ideal_saturates :
    massGap idealGram = Real.pi := mass_gap_ideal

section HadamardBound

open Complex Matrix

set_option maxHeartbeats 4000000

/-! ## 6. The Cauchy-Binet Identity and Cauchy-Schwarz

  The Cauchy-Binet identity for 2×3 complex matrices:
    normSq(∑ aᵢbᵢ) + ∑ normSq(cross_with_conj) = (∑|aᵢ|²)(∑|bᵢ|²)

  In pure ℝ form (12 variables), proved by ring.
  Cauchy-Schwarz follows by linarith + sq_nonneg.
-/

/-- The Cauchy-Binet identity in pure ℝ variables.
    This is the real-variable expansion of the complex identity
    normSq(∑ aᵢbᵢ) + ∑ normSq(aᵢ conj(bⱼ) - aⱼ conj(bᵢ)) = ‖a‖²‖b‖².
    Proof: polynomial identity verified by ring. -/
theorem cauchy_binet_for_products
    (p₀ q₀ p₁ q₁ p₂ q₂ r₀ s₀ r₁ s₁ r₂ s₂ : ℝ) :
    (p₀ * r₀ - q₀ * s₀ + (p₁ * r₁ - q₁ * s₁) + (p₂ * r₂ - q₂ * s₂)) ^ 2 +
    (p₀ * s₀ + q₀ * r₀ + (p₁ * s₁ + q₁ * r₁) + (p₂ * s₂ + q₂ * r₂)) ^ 2 +
    ((p₀ * r₁ + q₀ * s₁ - p₁ * r₀ - q₁ * s₀) ^ 2 +
     (q₀ * r₁ - p₀ * s₁ - q₁ * r₀ + p₁ * s₀) ^ 2) +
    ((p₀ * r₂ + q₀ * s₂ - p₂ * r₀ - q₂ * s₀) ^ 2 +
     (q₀ * r₂ - p₀ * s₂ - q₂ * r₀ + p₂ * s₀) ^ 2) +
    ((p₁ * r₂ + q₁ * s₂ - p₂ * r₁ - q₂ * s₁) ^ 2 +
     (q₁ * r₂ - p₁ * s₂ - q₂ * r₁ + p₂ * s₁) ^ 2)
    = (p₀ ^ 2 + q₀ ^ 2 + (p₁ ^ 2 + q₁ ^ 2) + (p₂ ^ 2 + q₂ ^ 2)) *
      (r₀ ^ 2 + s₀ ^ 2 + (r₁ ^ 2 + s₁ ^ 2) + (r₂ ^ 2 + s₂ ^ 2)) := by
  ring

/-- The Cauchy-Binet identity for cross products:
    ∑ normSq(aᵢ bⱼ - aⱼ bᵢ) + normSq(∑ aᵢ conj bᵢ) = (∑|aᵢ|²)(∑|bᵢ|²) -/
theorem cauchy_binet_for_cross
    (p₀ q₀ p₁ q₁ p₂ q₂ r₀ s₀ r₁ s₁ r₂ s₂ : ℝ) :
    ((p₀ * r₁ - q₀ * s₁ - (p₁ * r₀ - q₁ * s₀)) ^ 2 +
     (p₀ * s₁ + q₀ * r₁ - (p₁ * s₀ + q₁ * r₀)) ^ 2) +
    ((p₀ * r₂ - q₀ * s₂ - (p₂ * r₀ - q₂ * s₀)) ^ 2 +
     (p₀ * s₂ + q₀ * r₂ - (p₂ * s₀ + q₂ * r₀)) ^ 2) +
    ((p₁ * r₂ - q₁ * s₂ - (p₂ * r₁ - q₂ * s₁)) ^ 2 +
     (p₁ * s₂ + q₁ * r₂ - (p₂ * s₁ + q₂ * r₁)) ^ 2) +
    ((p₀ * r₀ + q₀ * s₀ + (p₁ * r₁ + q₁ * s₁) + (p₂ * r₂ + q₂ * s₂)) ^ 2 +
     (q₀ * r₀ - p₀ * s₀ + (q₁ * r₁ - p₁ * s₁) + (q₂ * r₂ - p₂ * s₂)) ^ 2)
    = (p₀ ^ 2 + q₀ ^ 2 + (p₁ ^ 2 + q₁ ^ 2) + (p₂ ^ 2 + q₂ ^ 2)) *
      (r₀ ^ 2 + s₀ ^ 2 + (r₁ ^ 2 + s₁ ^ 2) + (r₂ ^ 2 + s₂ ^ 2)) := by
  ring

/-- Cauchy-Schwarz for three complex products:
    |a₀b₀ + a₁b₁ + a₂b₂|² ≤ (∑|aᵢ|²)(∑|bᵢ|²). -/
theorem cauchy_schwarz_three (a0 a1 a2 b0 b1 b2 : ℂ) :
    normSq (a0 * b0 + a1 * b1 + a2 * b2)
    ≤ (normSq a0 + normSq a1 + normSq a2)
    * (normSq b0 + normSq b1 + normSq b2) := by
  obtain ⟨p₀, q₀⟩ := a0; obtain ⟨p₁, q₁⟩ := a1; obtain ⟨p₂, q₂⟩ := a2
  obtain ⟨r₀, s₀⟩ := b0; obtain ⟨r₁, s₁⟩ := b1; obtain ⟨r₂, s₂⟩ := b2
  simp only [normSq_apply, normSq_mk, mul_re, mul_im, add_re, add_im, sub_re, sub_im]
  have h := cauchy_binet_for_products p₀ q₀ p₁ q₁ p₂ q₂ r₀ s₀ r₁ s₁ r₂ s₂
  linarith [sq_nonneg (p₀ * r₁ + q₀ * s₁ - p₁ * r₀ - q₁ * s₀),
            sq_nonneg (q₀ * r₁ - p₀ * s₁ - q₁ * r₀ + p₁ * s₀),
            sq_nonneg (p₀ * r₂ + q₀ * s₂ - p₂ * r₀ - q₂ * s₀),
            sq_nonneg (q₀ * r₂ - p₀ * s₂ - q₂ * r₀ + p₂ * s₀),
            sq_nonneg (p₁ * r₂ + q₁ * s₂ - p₂ * r₁ - q₂ * s₁),
            sq_nonneg (q₁ * r₂ - p₁ * s₂ - q₂ * r₁ + p₂ * s₁)]

/-- Cross product norm bound:
    ∑|aᵢbⱼ - aⱼbᵢ|² ≤ (∑|aᵢ|²)(∑|bᵢ|²). -/
theorem cross_norm_bound (a0 a1 a2 b0 b1 b2 : ℂ) :
    normSq (a0 * b1 - a1 * b0)
    + normSq (a0 * b2 - a2 * b0)
    + normSq (a1 * b2 - a2 * b1)
    ≤ (normSq a0 + normSq a1 + normSq a2)
    * (normSq b0 + normSq b1 + normSq b2) := by
  obtain ⟨p₀, q₀⟩ := a0; obtain ⟨p₁, q₁⟩ := a1; obtain ⟨p₂, q₂⟩ := a2
  obtain ⟨r₀, s₀⟩ := b0; obtain ⟨r₁, s₁⟩ := b1; obtain ⟨r₂, s₂⟩ := b2
  simp only [normSq_apply, normSq_mk, mul_re, mul_im, add_re, add_im, sub_re, sub_im]
  have h := cauchy_binet_for_cross p₀ q₀ p₁ q₁ p₂ q₂ r₀ s₀ r₁ s₁ r₂ s₂
  linarith [sq_nonneg (p₀ * r₀ + q₀ * s₀ + (p₁ * r₁ + q₁ * s₁) + (p₂ * r₂ + q₂ * s₂)),
            sq_nonneg (q₀ * r₀ - p₀ * s₀ + (q₁ * r₁ - p₁ * s₁) + (q₂ * r₂ - p₂ * s₂))]

/-! ## 7. The Hadamard Determinant Bound

  THEOREM: For a 3×3 complex matrix with unit rows, |det V|² ≤ 1.

  Proof chain:
  1. Cofactor expansion: det V = V₀₀·C₀ + V₀₁·C₁ + V₀₂·C₂
  2. Cauchy-Schwarz: |det V|² ≤ (∑|V₀ⱼ|²)(∑|Cⱼ|²) = 1·∑|Cⱼ|²
  3. Each Cⱼ is a cross product of rows 1 and 2
  4. Cross bound: ∑|Cⱼ|² ≤ (∑|V₁ⱼ|²)(∑|V₂ⱼ|²) = 1
  5. Therefore: |det V|² ≤ 1

  This closes the last remaining assumption in the mass gap proof.
-/

/-- normSq(a - b) = normSq(b - a) -/
theorem normSq_sub_comm (a b : ℂ) : normSq (a - b) = normSq (b - a) := by
  rw [show b - a = -(a - b) from by ring, normSq_neg]

/-- THEOREM (Hadamard bound for 3×3 unit-row matrices):
    If ∑_j |V_{ij}|² = 1 for each row i, then |det V|² ≤ 1.
    DERIVED from the Cauchy-Binet identity (no axioms). -/
theorem hadamard_unit_rows (V : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ i : Fin 3, ∑ j : Fin 3, normSq (V i j) = 1) :
    normSq (Matrix.det V) ≤ 1 := by
  -- Expand det using the 3×3 formula
  rw [det_fin_three]
  -- Regroup into cofactor expansion
  have hrw : V 0 0 * V 1 1 * V 2 2 - V 0 0 * V 1 2 * V 2 1
      - V 0 1 * V 1 0 * V 2 2 + V 0 1 * V 1 2 * V 2 0
      + V 0 2 * V 1 0 * V 2 1 - V 0 2 * V 1 1 * V 2 0
      = V 0 0 * (V 1 1 * V 2 2 - V 1 2 * V 2 1)
      + V 0 1 * (V 1 2 * V 2 0 - V 1 0 * V 2 2)
      + V 0 2 * (V 1 0 * V 2 1 - V 1 1 * V 2 0) := by ring
  rw [hrw]
  -- Extract unit row conditions
  have h0 : normSq (V 0 0) + normSq (V 0 1) + normSq (V 0 2) = 1 := by
    have := h 0; simp [Fin.sum_univ_three] at this; linarith
  have h1 : normSq (V 1 0) + normSq (V 1 1) + normSq (V 1 2) = 1 := by
    have := h 1; simp [Fin.sum_univ_three] at this; linarith
  have h2 : normSq (V 2 0) + normSq (V 2 1) + normSq (V 2 2) = 1 := by
    have := h 2; simp [Fin.sum_univ_three] at this; linarith
  -- Cauchy-Schwarz on row 0 and cofactors
  have hCS := cauchy_schwarz_three (V 0 0) (V 0 1) (V 0 2)
    (V 1 1 * V 2 2 - V 1 2 * V 2 1)
    (V 1 2 * V 2 0 - V 1 0 * V 2 2)
    (V 1 0 * V 2 1 - V 1 1 * V 2 0)
  -- Cross product bound on rows 1 and 2
  have hCross := cross_norm_bound (V 1 0) (V 1 1) (V 1 2) (V 2 0) (V 2 1) (V 2 2)
  -- Match cofactors to cross products (normSq ignores sign)
  have hCofEq : normSq (V 1 1 * V 2 2 - V 1 2 * V 2 1)
      + normSq (V 1 2 * V 2 0 - V 1 0 * V 2 2)
      + normSq (V 1 0 * V 2 1 - V 1 1 * V 2 0)
      = normSq (V 1 0 * V 2 1 - V 1 1 * V 2 0)
      + normSq (V 1 0 * V 2 2 - V 1 2 * V 2 0)
      + normSq (V 1 1 * V 2 2 - V 1 2 * V 2 1) := by
    rw [normSq_sub_comm (V 1 2 * V 2 0) (V 1 0 * V 2 2)]; ring
  rw [h0] at hCS; rw [h1, h2] at hCross; rw [hCofEq] at hCS
  linarith

end HadamardBound

end DRLT.YangMills
