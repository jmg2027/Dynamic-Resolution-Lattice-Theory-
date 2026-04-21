import E213.Research.ZSqrt2
import E213.Research.IntHelpers
import E213.Tactic.QuadNorm

open E213.Research.IntHelpers
open E213.Tactic

/-!
# Research: `ℤ[√-2]` integral domain + conj ring homomorphism

Multiplicativity of `normSq` (with factor 2 from `(√-2)²`),
integral-domain property, and the fact that `conj` distributes
over multiplication — all via `simp`+`omega` (no `ring`).
-/

namespace E213.Research.Z2

theorem mul_comm (u v : Z2) : u * v = v * u := by
  apply ext
  · show u.re * v.re - 2 * (u.im * v.im)
       = v.re * u.re - 2 * (v.im * u.im)
    rw [Int.mul_comm u.re v.re, Int.mul_comm u.im v.im]
  · show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [Int.mul_comm u.re v.im, Int.mul_comm u.im v.re, Int.add_comm]

/-- `|uv|² = |u|²·|v|²` in `ℤ[√-2]`. -/
theorem normSq_mul (u v : Z2) :
    (u * v).normSq = u.normSq * v.normSq := by
  show (u.re*v.re - 2*(u.im*v.im))*(u.re*v.re - 2*(u.im*v.im))
     + 2*((u.re*v.im + u.im*v.re)*(u.re*v.im + u.im*v.re))
     = (u.re*u.re + 2*(u.im*u.im)) * (v.re*v.re + 2*(v.im*v.im))
  quad_norm

/-- `conj` distributes over multiplication in `ℤ[√-2]`. -/
theorem conj_mul (u v : Z2) : conj (u * v) = conj u * conj v := by
  apply ext
  · show u.re * v.re - 2 * (u.im * v.im)
       = u.re * v.re - 2 * ((-u.im) * (-v.im))
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
  · show -(u.re * v.im + u.im * v.re)
       = u.re * (-v.im) + (-u.im) * v.re
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_add]

theorem conj_I : Z2.conj I = negI := rfl

theorem conj_negI : Z2.conj negI = I := by
  show (⟨0, -(-1)⟩ : Z2) = ⟨0, 1⟩
  apply ext <;> simp

end E213.Research.Z2

namespace E213.Research.Z2

theorem normSq_nonneg (u : Z2) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + 2 * (u.im * u.im)
  have h1 := IntHelpers.mul_self_nonneg u.re
  have h2 := IntHelpers.mul_self_nonneg u.im
  omega

theorem normSq_eq_zero_iff (u : Z2) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have h_eq : u.re * u.re + 2 * (u.im * u.im) = 0 := h
    have hre : u.re * u.re = 0 := by omega
    have him : u.im * u.im = 0 := by omega
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + 2 * (0 * 0) = 0
    simp

theorem no_zero_div (u v : Z2) : u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 + 2 * (0 * 0) = 0; simp
  rw [normSq_mul] at hn
  rcases Int.mul_eq_zero.mp hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff v).mp h)

theorem mul_ne_zero_of_ne_zero {u v : Z2} (hu : u ≠ 0) (hv : v ≠ 0) :
    u * v ≠ 0 := fun h => (no_zero_div u v h).elim hu hv

end E213.Research.Z2
