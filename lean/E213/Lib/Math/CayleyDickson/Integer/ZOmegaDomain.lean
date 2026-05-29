import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Meta.Nat.IntHelpers
import E213.Meta.Tactic.QuadNorm

open E213.Meta.Nat
open E213.Meta.Nat.IntHelpers
open E213.Tactic

/-!
# `ℤ[ω]` integral domain (Eisenstein)

`quad_norm` macro for `normSq_mul`.  `normSq_nonneg` uses
`2·(a² - ab + b²) = a² + b² + (a + -b)²`.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega


/-- `|uv|² = |u|²·|v|²` for the Eisenstein norm.  Typeclass projection
    through `IntegerNormed213.normSq_mul` — `[propext]`-only purity
    (the previous `quad_norm`-based proof leaked `[propext, Quot.sound]`
    via simp + omega). -/
theorem normSq_mul (u v : ZOmega) :
    (u * v).normSq = u.normSq * v.normSq :=
  E213.Meta.Algebra213.IntegerNormed213.normSq_mul u v

/-- `conj` distributes over multiplication. -/
theorem conj_mul (u v : ZOmega) :
    conj (u * v) = conj u * conj v := by
  apply ext
  · show (u.re*v.re - u.im*v.im)
        - (u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(v.re - v.im) - (-u.im)*(-v.im)
    simp only [E213.Meta.Int213.sub_mul, E213.Meta.Int213.mul_sub, Int.neg_mul,
               Int.mul_neg, Int.neg_neg]
    omega
  · show -(u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(-v.im) + (-u.im)*(v.re - v.im)
         - (-u.im)*(-v.im)
    simp only [E213.Meta.Int213.sub_mul, E213.Meta.Int213.mul_sub, Int.neg_mul,
               Int.mul_neg, Int.neg_neg]
    omega

/-- Sign-case analysis on `re*im`: 0 ≤ a² - ab + b². -/
theorem normSq_nonneg (u : ZOmega) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re - u.re * u.im + u.im * u.im
  have h_a2 := IntHelpers.mul_self_nonneg u.re
  have h_b2 := IntHelpers.mul_self_nonneg u.im
  by_cases hab : 0 ≤ u.re * u.im
  · -- 0 ≤ ab.  Use (a - b)² = a² - 2ab + b² ≥ 0.
    have h_sub := IntHelpers.mul_self_nonneg (u.re - u.im)
    have h_exp : (u.re - u.im) * (u.re - u.im)
               = u.re*u.re - 2*(u.re*u.im) + u.im*u.im := by
      have : (u.re - u.im) * (u.re - u.im)
           = u.re*u.re - u.re*u.im - (u.im*u.re - u.im*u.im) := by
        rw [E213.Meta.Int213.sub_mul, E213.Meta.Int213.mul_sub, E213.Meta.Int213.mul_sub]
      rw [this, Int.mul_comm u.im u.re]
      omega
    omega
  · -- ab < 0.  Direct: a² + b² + (-ab) all ≥ 0.
    omega

theorem normSq_eq_zero_iff (u : ZOmega) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re * u.re - u.re * u.im + u.im * u.im = 0 := h
    have h_a2 := IntHelpers.mul_self_nonneg u.re
    have h_b2 := IntHelpers.mul_self_nonneg u.im
    -- Case-split on sign of ab to derive a*a = 0 ∧ b*b = 0
    have h_ab : u.re * u.im = 0 := by
      by_cases hab : 0 ≤ u.re * u.im
      · -- (a-b)² = a²-2ab+b² ≥ 0, with normSq=0 → a²+b²=ab → 2ab=2(a²+b²)/(...)...
        -- Use: 0 = a²+b²-ab and 2ab ≤ a²+b² (from (a-b)²≥0)
        have h_sub := IntHelpers.mul_self_nonneg (u.re - u.im)
        have h_exp : (u.re - u.im) * (u.re - u.im)
                   = u.re*u.re - 2*(u.re*u.im) + u.im*u.im := by
          have : (u.re - u.im) * (u.re - u.im)
               = u.re*u.re - u.re*u.im - (u.im*u.re - u.im*u.im) := by
            rw [E213.Meta.Int213.sub_mul, E213.Meta.Int213.mul_sub, E213.Meta.Int213.mul_sub]
          rw [this, Int.mul_comm u.im u.re]
          omega
        omega
      · omega
    have h_a2_eq : u.re * u.re = 0 := by omega
    have h_b2_eq : u.im * u.im = 0 := by omega
    have h_re : u.re = 0 := IntHelpers.mul_self_eq_zero.mp h_a2_eq
    have h_im : u.im = 0 := IntHelpers.mul_self_eq_zero.mp h_b2_eq
    exact ext h_re h_im
  · rintro rfl
    show (0 : Int) * 0 - 0 * 0 + 0 * 0 = 0
    simp

theorem no_zero_div (u v : ZOmega) : u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 - 0 * 0 + 0 * 0 = 0; simp
  rw [normSq_mul] at hn
  rcases Int.mul_eq_zero.mp hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff v).mp h)

end E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega
