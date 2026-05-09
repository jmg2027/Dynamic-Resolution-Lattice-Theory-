import E213.Lib.Math.CayleyDickson.ZSqrt
import E213.Lib.Math.NatHelpers.IntHelpers
import E213.Term.Tactic.QuadNorm
import E213.Theory.Internal.Int213

open E213.Lib.Math.NatHelpers
open E213.Lib.Math.NatHelpers.IntHelpers
open E213.Tactic

/-!
# parametric `ZSqrt D` integral-domain properties

Generic proofs over `D : Int`.  `normSq_nonneg`,
`normSq_eq_zero_iff`, and `no_zero_div` carry a hypothesis
`0 ≤ D` (positive-semidefinite norm).
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrt.ZSqrt


variable {D : Int}

theorem mul_comm (u v : ZSqrt D) : u * v = v * u := by
  apply ext
  · show u.re * v.re - D * (u.im * v.im)
       = v.re * u.re - D * (v.im * u.im)
    rw [E213.Theory.Internal.Int213.mul_comm u.re v.re,
        E213.Theory.Internal.Int213.mul_comm u.im v.im]
  · show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [E213.Theory.Internal.Int213.mul_comm u.re v.im,
        E213.Theory.Internal.Int213.mul_comm u.im v.re,
        E213.Theory.Internal.Int213.add_comm]

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
    have h : (-u.im) * (-v.im) = u.im * v.im := by
      rw [E213.Theory.Internal.Int213.neg_mul,
          E213.Theory.Internal.Int213.mul_neg, Int.neg_neg]
    rw [h]
  · show -(u.re * v.im + u.im * v.re)
       = u.re * (-v.im) + (-u.im) * v.re
    rw [E213.Theory.Internal.Int213.mul_neg,
        E213.Theory.Internal.Int213.neg_mul,
        ← E213.Theory.Internal.Int213.neg_add]

theorem normSq_nonneg (hD : 0 ≤ D) (u : ZSqrt D) :
    0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + D * (u.im * u.im)
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  have h3 : 0 ≤ D * (u.im * u.im) :=
    E213.Theory.Internal.Int213.mul_nonneg hD h2
  exact E213.Theory.Internal.Int213.add_nonneg h1 h3

variable {D : Int}

theorem normSq_eq_zero_iff (hD : 0 < D) (u : ZSqrt D) :
    u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re * u.re + D * (u.im * u.im) = 0 := h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    -- Convert 0 < D to 0 ≤ D via case analysis on D
    have hDnn : (0 : Int) ≤ D := match D, hD with
      | .ofNat _, _ => Int.ofNat_nonneg _
      | .negSucc _, h => by cases h
    have h3 : 0 ≤ D * (u.im * u.im) :=
      E213.Theory.Internal.Int213.mul_nonneg hDnn h2
    obtain ⟨hre, hd_im⟩ :=
      E213.Theory.Internal.Int213.add_eq_zero_of_nonneg h1 h3 h_eq
    have him : u.im * u.im = 0 := by
      rcases E213.Theory.Internal.Int213.mul_eq_zero hd_im with hD0 | h
      · exfalso; rw [hD0] at hD; cases hD
      · exact h
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + D * (0 * 0) = 0
    -- 0 * 0 = 0 (rfl), then D * 0 = 0 (mul_zero), then 0 + 0 = 0 (add_zero)
    show (0 : Int) + D * 0 = 0
    rw [Int.mul_zero, Int.add_zero]

theorem no_zero_div (hD : 0 < D) (u v : ZSqrt D) :
    u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 + D * (0 * 0) = 0; simp
  rw [normSq_mul] at hn
  rcases Int.mul_eq_zero.mp hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff hD u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff hD v).mp h)

end E213.Lib.Math.CayleyDickson.ZSqrt.ZSqrt
