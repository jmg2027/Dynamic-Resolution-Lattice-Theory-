import E213.Lib.Math.CayleyDickson.ZI
import E213.Lib.Math.NatHelpers.IntHelpers
import E213.Lib.Math.CayleyDickson.QuadIdentities
import E213.Meta.Int213.Core

open E213.Lib.Math.NatHelpers
open E213.Lib.Math.NatHelpers.IntHelpers
open E213.Lib.Math.CayleyDickson.QuadIdentities

/-!
# `ZI` integral-domain properties

`ZI.mul_comm`, `ZI.normSq_mul` (Diophantus identity),
`ZI.normSq_nonneg`, `ZI.normSq_eq_zero_iff`, `ZI.no_zero_div`.
Core Lean 4 only, no `ring`; `normSq_mul`'s polynomial identity
is closed by `simp` with AC-arith + `omega` for cross-term
cancellation.
-/

namespace E213.Lib.Math.CayleyDickson.ZI.ZI


theorem mul_comm (u v : ZI) : u * v = v * u := by
  apply ext
  · show u.re * v.re - u.im * v.im = v.re * u.re - v.im * u.im
    rw [E213.Theory.Internal.Int213.mul_comm u.re v.re,
        E213.Theory.Internal.Int213.mul_comm u.im v.im]
  · show u.re * v.im + u.im * v.re = v.re * u.im + v.im * u.re
    rw [E213.Theory.Internal.Int213.mul_comm u.re v.im,
        E213.Theory.Internal.Int213.mul_comm u.im v.re,
        E213.Theory.Internal.Int213.add_comm]

/-- **Diophantus identity.** `|uv|² = |u|² · |v|²`. -/
theorem normSq_mul (u v : ZI) :
    (u * v).normSq = u.normSq * v.normSq := by
  show (u.re*v.re - u.im*v.im)*(u.re*v.re - u.im*v.im)
     + (u.re*v.im + u.im*v.re)*(u.re*v.im + u.im*v.re)
     = (u.re*u.re + u.im*u.im) * (v.re*v.re + v.im*v.im)
  exact int_quad_diophantus u.re u.im v.re v.im

theorem normSq_nonneg (u : ZI) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re + u.im * u.im
  exact E213.Theory.Internal.Int213.add_nonneg
    (IntHelpers.mul_self_nonneg u.re) (IntHelpers.mul_self_nonneg u.im)

theorem normSq_eq_zero_iff (u : ZI) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := IntHelpers.mul_self_nonneg u.re
    have h2 := IntHelpers.mul_self_nonneg u.im
    have h_eq : u.re * u.re + u.im * u.im = 0 := h
    obtain ⟨hre, him⟩ :=
      E213.Theory.Internal.Int213.add_eq_zero_of_nonneg h1 h2 h_eq
    apply ext
    · exact IntHelpers.mul_self_eq_zero.mp hre
    · exact IntHelpers.mul_self_eq_zero.mp him
  · rintro rfl
    show (0 : Int) * 0 + 0 * 0 = 0
    rfl

/-- **Integral-domain property.** `ZI.mul` has no zero divisors. -/
theorem no_zero_div (u v : ZI) : u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 + 0 * 0 = 0; rfl
  rw [normSq_mul] at hn
  rcases E213.Theory.Internal.Int213.mul_eq_zero hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff v).mp h)

theorem mul_ne_zero_of_ne_zero {u v : ZI} (hu : u ≠ 0) (hv : v ≠ 0) :
    u * v ≠ 0 := fun h => (no_zero_div u v h).elim hu hv

end E213.Lib.Math.CayleyDickson.ZI.ZI
