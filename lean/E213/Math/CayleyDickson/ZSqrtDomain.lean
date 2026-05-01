import E213.Math.CayleyDickson.ZSqrt
import E213.Math.IntHelpers
import E213.Tactic.QuadNorm

open E213.Math.IntHelpers
open E213.Tactic

/-!
# Research: parametric `ZSqrt D` integral-domain properties

Generic proofs over `D : Int`.  `normSq_nonneg`,
`normSq_eq_zero_iff`, and `no_zero_div` carry a hypothesis
`0 ≤ D` (positive-semidefinite norm).
-/

namespace E213.Math.CayleyDickson.ZSqrtDomain

variable {D : Int}

theorem mul_comm (u v : ZSqrt D) : u * v = v * u := by
  apply ext
  · show u.re * v.re - D * (u.im * v.im)
       = v.re * u.re - D * (v.im * u.im)
    rw [Int.mul_comm u.re v.re, Int.mul_comm u.im v.im]
  · show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [Int.mul_comm u.re v.im, Int.mul_comm u.im v.re,
        Int.add_comm]

/-- `|uv|² = |u|²·|v|²` for any `D`. -/
theorem normSq_mul (u v : ZSqrt D) :
    (u * v).normSq = u.normSq * v.normSq := by
  show (u.re*v.re - D*(u.im*v.im))*(u.re*v.re - D*(u.im*v.im))
     + D*((u.re*v.im + u.im*v.re)*(u.re*v.im + u.im*v.re))
     = (u.re*u.re + D*(u.im*u.im)) * (v.re*v.re + D*(v.im*v.im))
  quad_norm

/-- `conj` distributes over multiplication. -/
theorem conj_mul (u v : ZSqrt D) :
    conj (u * v) = conj u * conj v := by
  apply ext
  · show u.re * v.re - D * (u.im * v.im)
       = u.re * v.re - D * ((-u.im) * (-v.im))
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  · show -(u.re * v.im + u.im * v.re)
       = u.re * (-v.im) + (-u.im) * v.re
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_add]

theorem normSq_nonneg (hD : 0 ≤ D) (u : ZSqrt D) :
    0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + D * (u.im * u.im)
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  have h3 : 0 ≤ D * (u.im * u.im) := Int.mul_nonneg hD h2
  omega

end E213.Math.CayleyDickson.ZSqrtDomain

namespace E213.Math.CayleyDickson.ZSqrtDomain

variable {D : Int}

theorem normSq_eq_zero_iff (hD : 0 < D) (u : ZSqrt D) :
    u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re * u.re + D * (u.im * u.im) = 0 := h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have hDnn : (0 : Int) ≤ D := by omega
    have h3 : 0 ≤ D * (u.im * u.im) := Int.mul_nonneg hDnn h2
    have hre : u.re * u.re = 0 := by omega
    have hd_im : D * (u.im * u.im) = 0 := by omega
    have him : u.im * u.im = 0 := by
      rcases Int.mul_eq_zero.mp hd_im with h | h
      · omega
      · exact h
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + D * (0 * 0) = 0
    simp

theorem no_zero_div (hD : 0 < D) (u v : ZSqrt D) :
    u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 + D * (0 * 0) = 0; simp
  rw [normSq_mul] at hn
  rcases Int.mul_eq_zero.mp hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff hD u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff hD v).mp h)

end E213.Math.CayleyDickson.ZSqrtDomain
