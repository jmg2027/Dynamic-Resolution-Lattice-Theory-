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

end DRLT.YangMills
