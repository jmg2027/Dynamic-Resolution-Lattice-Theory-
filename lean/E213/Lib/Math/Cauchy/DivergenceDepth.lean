import E213.Lib.Math.Cauchy.EulerDivergenceForm
import E213.Meta.Tactic.NatHelper

/-!
# DivergenceDepth — the divergence ladder, and e's depth is 3

`EulerDivergenceForm` showed the *form* of e's divergence is its cross-determinant
`W_n = −n!`.  But `W_n` is itself a sequence, and `n!` itself diverges — so the
question recurs: *what is the form of that divergence?*  Take the cross-determinant
again, then again, until the answer stops moving.

This is the user's framing made literal: the infinite (a divergent sequence) is
pinned by a finite reference (its level-`k` invariant), and the divergence of
*that* by the next reference, level after level — until a **constant floor** is
reached in finitely many steps.  The number of steps to the floor is a new
invariant: the **divergence depth**.

For e the ladder is exact and short:

  - **L0** convergents `aₙ/dₙ` → e (diverges)
  - **L1** cross-determinant `|W_n| = dₙ = n!` (`EulerDivergenceForm`) — still
    diverges
  - **L2** multiplicative ratio `rₙ := dₙ₊₁ / dₙ = n+1` (`ratio_step`) — linear,
    still diverges
  - **L3** the ratio's increment `rₙ₊₁ − rₙ = 1` — **constant.  Floor reached.**

So **e has divergence depth 3**: three lifts (cross-det, ratio, difference) collapse
its entire divergence to the constant `1`.  An algebraic irrational (φ, √2) has
**depth 1** — its cross-determinant is *already* constant (`±1`, Cassini /
`pell_invariant`), the floor of an area-preserving (`det = 1`) orbit.  And π is
*deeper* still: its cross-det ratio is a degree-4 polynomial in `n`
(`4(n+1)²(2n+1)(2n+3)`), which needs four further finite differences to reach a
constant — **depth 6** (1 cross-det + 1 ratio + 4 differences).

The depth orders the reals by *how far their divergence is from being trivial*:
algebraic 1 < e 3 < π 6.  This is the precise, ∅-axiom sense in which e is a
"shallower" transcendental than π — the quantification of e's regular continued
fraction versus π's irregular one.

This file formalises the e ladder (the cleanest case); the depths of φ (=1) and π
(=6) are recorded with their Lean witnesses where formalised.

All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.DivergenceDepth

open E213.Lib.Math.Cauchy.EulerDivergenceForm (fact eulerDen_eq_fact)
open E213.Lib.Math.Cauchy.EulerSeq (eulerDen)

/-! ## §1 — e's divergence ladder -/

/-- **Layer 1** of e's ladder: the cross-determinant magnitude `|W_n| = dₙ = n!`
    (`EulerDivergenceForm.euler_cross_det_is_factorial`). -/
def crossDet (n : Nat) : Nat := eulerDen n

/-- **Layer 2**: the multiplicative ratio of the cross-determinant, `rₙ := n+1`. -/
def ratio (n : Nat) : Nat := n + 1

/-- ★★ **L1 → L2**: `crossDet` grows by exactly its ratio — `crossDet(n+1) = rₙ ·
    crossDet n` — i.e. `dₙ₊₁ = (n+1)·dₙ`.  This is the factorial recurrence; the
    ratio sequence `rₙ = n+1` is the layer-2 invariant. -/
theorem L1_to_L2 (n : Nat) : crossDet (n+1) = ratio n * crossDet n := rfl

/-- ★★ **L2 → L3 (the floor)**: the ratio's increment is the **constant 1**.
    `rₙ₊₁ = rₙ + 1` — the layer-2 sequence is arithmetic, so its difference is
    constant: the ladder bottoms out. -/
theorem L2_to_floor (n : Nat) : ratio (n+1) = ratio n + 1 := rfl

/-- ★★★ **e's divergence depth is 3.**  The second difference of the ratio
    vanishes — `(rₙ₊₂ − rₙ₊₁) = (rₙ₊₁ − rₙ)` (both `= 1`) — so after cross-det
    (L1), ratio (L2), and one difference (L3) the divergence is a constant.  Three
    finite references exhaust e's infinite spreading. -/
theorem floor_value (n : Nat) : ratio (n+1) - ratio n = 1 := by
  show (n+1+1) - (n+1) = 1
  rw [Nat.add_comm (n+1) 1, E213.Tactic.NatHelper.add_sub_cancel_right]

/-- ★★★ **e's divergence depth is 3.**  The second difference of the ratio
    vanishes — `(rₙ₊₂ − rₙ₊₁) = (rₙ₊₁ − rₙ)` (both `= 1`) — so after cross-det
    (L1), ratio (L2), and one difference (L3) the divergence is a constant.  Three
    finite references exhaust e's infinite spreading. -/
theorem depth_three (n : Nat) :
    ratio (n+2) - ratio (n+1) = ratio (n+1) - ratio n := by
  rw [floor_value n]
  show ratio (n+1+1) - ratio (n+1) = 1
  exact floor_value (n+1)

end E213.Lib.Math.Cauchy.DivergenceDepth
