import E213.Lib.Math.CayleyDickson.ZSqrt2
import E213.Lib.Math.NatHelpers.IntHelpers
import E213.Lib.Math.CayleyDickson.QuadIdentities
import E213.Meta.Int213.Core

open E213.Lib.Math.NatHelpers
open E213.Lib.Math.NatHelpers.IntHelpers
open E213.Lib.Math.CayleyDickson.QuadIdentities

/-!
# `ℤ[√-2]` integral domain + conj ring homomorphism

∅-axiom — `Int.{mul_comm, add_comm, neg_mul, mul_neg, neg_add,
mul_nonneg, add_nonneg, mul_eq_zero}` replaced with `Int213` PURE
versions; `Iff.mp` / `simp` chains rewritten.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrt2.Z2


open E213.Lib.Math.CayleyDickson.ZSqrt2

theorem mul_comm (u v : Z2) : u * v = v * u := by
  apply ext
  · show u.re * v.re - 2 * (u.im * v.im)
       = v.re * u.re - 2 * (v.im * u.im)
    rw [E213.Theory.Internal.Int213.mul_comm u.re v.re,
        E213.Theory.Internal.Int213.mul_comm u.im v.im]
  · show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [E213.Theory.Internal.Int213.mul_comm u.re v.im,
        E213.Theory.Internal.Int213.mul_comm u.im v.re,
        E213.Theory.Internal.Int213.add_comm]

/-- `|uv|² = |u|²·|v|²` in `ℤ[√-2]`. -/
theorem normSq_mul (u v : Z2) :
    (u * v).normSq = u.normSq * v.normSq := by
  show (u.re*v.re - 2*(u.im*v.im))*(u.re*v.re - 2*(u.im*v.im))
     + 2*((u.re*v.im + u.im*v.re)*(u.re*v.im + u.im*v.re))
     = (u.re*u.re + 2*(u.im*u.im)) * (v.re*v.re + 2*(v.im*v.im))
  exact int_quad_diophantus_sqrt2 u.re u.im v.re v.im

/-- `conj` distributes over multiplication in `ℤ[√-2]`. -/
theorem conj_mul (u v : Z2) : conj (u * v) = conj u * conj v := by
  apply ext
  · show u.re * v.re - 2 * (u.im * v.im)
       = u.re * v.re - 2 * ((-u.im) * (-v.im))
    have h : (-u.im) * (-v.im) = u.im * v.im := by
      rw [E213.Theory.Internal.Int213.neg_mul,
          E213.Theory.Internal.Int213.mul_neg, Int.neg_neg]
    rw [h]
  · show -(u.re * v.im + u.im * v.re)
       = u.re * (-v.im) + (-u.im) * v.re
    rw [E213.Theory.Internal.Int213.mul_neg,
        E213.Theory.Internal.Int213.neg_mul,
        ← E213.Theory.Internal.Int213.neg_add]

theorem conj_I : Z2.conj I = negI := rfl

theorem conj_negI : Z2.conj negI = I := by
  apply ext
  · show (0 : Int) = 0; rfl
  · show -(-1 : Int) = 1; exact Int.neg_neg _

theorem normSq_nonneg (u : Z2) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + 2 * (u.im * u.im)
  exact E213.Theory.Internal.Int213.add_nonneg
    (IntHelpers.mul_self_nonneg u.re)
    (E213.Theory.Internal.Int213.mul_nonneg
      (by decide) (IntHelpers.mul_self_nonneg u.im))

theorem normSq_eq_zero_iff (u : Z2) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have h_eq : u.re * u.re + 2 * (u.im * u.im) = 0 := h
    have h2_imim : 0 ≤ 2 * (u.im * u.im) :=
      E213.Theory.Internal.Int213.mul_nonneg (by decide) h2
    obtain ⟨hre, h_2im⟩ :=
      E213.Theory.Internal.Int213.add_eq_zero_of_nonneg h1 h2_imim h_eq
    -- 2 * (u.im * u.im) = 0 → u.im * u.im = 0
    have him : u.im * u.im = 0 := by
      rcases E213.Theory.Internal.Int213.mul_eq_zero h_2im with h | h
      · exact absurd h (by decide)
      · exact h
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + 2 * (0 * 0) = 0
    rfl

theorem no_zero_div (u v : Z2) : u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 + 2 * (0 * 0) = 0; rfl
  rw [normSq_mul] at hn
  rcases E213.Theory.Internal.Int213.mul_eq_zero hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff v).mp h)

theorem mul_ne_zero_of_ne_zero {u v : Z2} (hu : u ≠ 0) (hv : v ≠ 0) :
    u * v ≠ 0 := fun h => (no_zero_div u v h).elim hu hv

end E213.Lib.Math.CayleyDickson.ZSqrt2.Z2
