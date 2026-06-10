import E213.Lib.Math.Analysis.ODE.HeatEq.Discrete
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Meta.Nat.PolyNatMTactic

/-!
# The maximum principle as a `Real213` cut inequality (∅-axiom)

The discrete maximum principle (`heatIter_range`) is a `Nat` statement about the
numerator-tracked field: data in `[A, B]` keeps the `t`-step field in `[2ᵗA, 2ᵗB]`.
The *averaged* field at site `x` and time `t` is the rational `heatIter n t u x / 2ᵗ` —
a genuine `Real213` cut, `constCut (heatIter n t u x) (2ᵗ)`.  This file promotes the
maximum principle to that level: **the heat field, as a point of the `Real213` line,
stays in the order interval `[A, B]` for all time** (`heat_max_principle_real`) —
`‖u(t)‖∞ ≤ ‖u(0)‖∞` in the completed real order, the parabolic maximum principle with
the mesh-uniform constant carried by the cut itself.

Tool: `constCut_le_constCut`, the cross-multiplied order bridge `a·d ≤ c·b ⟹
constCut a b ≤ constCut c d` (`d > 0`) — the generic `ℚ`-to-cut order embedding.
-/

namespace E213.Lib.Math.Analysis.ODE.HeatEq.MaxPrincipleReal

open E213.Lib.Math.Analysis.ODE.HeatEq.Discrete (heatIter heatIter_range)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutLe)

/-- ★★★ **Cross-multiplied order bridge**: `a·d ≤ c·b` (i.e. `a/b ≤ c/d`) with `d > 0`
    gives `constCut a b ≤ constCut c d` in the cut order — the order-embedding of
    rational comparison into `Real213` cuts, division-free. -/
theorem constCut_le_constCut (a b c d : Nat) (hd : 0 < d) (h : a * d ≤ c * b) :
    cutLe (constCut a b) (constCut c d) := by
  intro m k hk
  have hck : c * k ≤ d * m := of_decide_eq_true hk
  apply decide_eq_true
  have hchain : d * (a * k) ≤ d * (b * m) := by
    have h2 : (a * d) * k ≤ (c * b) * k := Nat.mul_le_mul h (Nat.le_refl k)
    have h4 : b * (c * k) ≤ b * (d * m) := Nat.mul_le_mul (Nat.le_refl b) hck
    calc d * (a * k) = (a * d) * k := by ring_nat
      _ ≤ (c * b) * k := h2
      _ = b * (c * k) := by ring_nat
      _ ≤ b * (d * m) := h4
      _ = d * (b * m) := by ring_nat
  exact Nat.le_of_mul_le_mul_left hchain hd

/-- ★★★★★ **The `Real213`-cut maximum principle**: for data in `[A, B]`, the time-`t`
    averaged heat field at every site — the `Real213` cut `heatIter n t u x / 2ᵗ` —
    satisfies `A ≤ field ≤ B` in the genuine cut order, for **all** `t` and every mesh
    `n`.  The discrete maximum principle (`heatIter_range`) promoted to the completed
    line: the heat semigroup is a sup-norm contraction as an operator on `Real213`-valued
    data.  (Frontier brick: `ricci_flow_smooth_core.md`, the `Real213`-cut maximum
    principle.) -/
theorem heat_max_principle_real (n A B t : Nat) (u : Nat → Nat)
    (hlo : ∀ y, A ≤ u y) (hhi : ∀ y, u y ≤ B) (x : Nat) :
    cutLe (constCut A 1) (constCut (heatIter n t u x) (2 ^ t))
    ∧ cutLe (constCut (heatIter n t u x) (2 ^ t)) (constCut B 1) := by
  obtain ⟨hge, hle⟩ := heatIter_range n A B t u hlo hhi x
  have hpow : 0 < 2 ^ t := Nat.pos_pow_of_pos t (by decide)
  constructor
  · apply constCut_le_constCut A 1 (heatIter n t u x) (2 ^ t) hpow
    exact Nat.le_trans (Nat.le_of_eq (Nat.mul_comm A (2 ^ t)))
      (Nat.le_trans hge (Nat.le_of_eq (Nat.mul_one _).symm))
  · apply constCut_le_constCut (heatIter n t u x) (2 ^ t) B 1 (by decide)
    exact Nat.le_trans (Nat.le_of_eq (Nat.mul_one _))
      (Nat.le_trans hle (Nat.le_of_eq (Nat.mul_comm (2 ^ t) B)))

end E213.Lib.Math.Analysis.ODE.HeatEq.MaxPrincipleReal
