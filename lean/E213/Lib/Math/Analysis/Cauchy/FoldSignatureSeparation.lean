import E213.Lib.Math.Analysis.Cauchy.HurwitzianCF

/-!
# FoldSignatureSeparation — the additive-fold and multiplicative-fold signatures are independent

A sequence carries two finite signatures, the two `invert`-folds of `G188`:

  * the **additive-fold depth** — `reachesFloor s` (`∃ k, Δ^k s` constant): annihilation
    order under the *specific* operator `Δ = E − 1`.  Finite iff `s` is a discrete
    polynomial.
  * the **multiplicative-fold order** — the order of the *best* constant-coefficient
    linear recurrence `s` closes into.  Here at its bottom rung: `LinRec1 q s`
    (`s(n+1) = q·s(n)`), order-1 C-finite.

These measure different things (annihilation by `Δ`-powers vs by the best constant-coefficient
operator), and the no-exterior doctrine predicts the cross-relation is the content.  This file
pins them **independent**: C-finite order does **not** determine difference-depth.

> ★★★ `order_does_not_bound_depth` : two **order-1** C-finite sequences with **opposite**
> difference-depth — the constant `1` (depth `0`) and the geometric `2ⁿ` (depth `∞`,
> `geom_infinite_depth`).  Same multiplicative-fold rank, maximally different additive-fold
> depth: order `1` bounds the depth of neither.

The witness `2ⁿ` is exactly the founding invert-twin read at the sequence scale: its
multiplicative fold closes at rank `1` (`2ⁿ⁺¹ = 2·2ⁿ`) while its additive fold never floors
(`Δ`-re-pointing produces fresh distinction forever).  The annihilator that kills `2ⁿ` is
`E − 2` (order 1), **not** any power of `Δ = E − 1` — which is *why* the difference-depth is
infinite though the C-finite order is `1`.  (Difference-depth ⟹ C-finite — `Δ^{d+1}` is a
constant-coefficient recurrence, `polyDepth_diff_recurrence` — is the containment direction;
`2ⁿ` witnesses that it is strict.)

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.FoldSignatureSeparation

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (reachesFloor)
open E213.Lib.Math.Analysis.Cauchy.HurwitzianCF (geom_infinite_depth)

/-- **Order-1 homogeneous constant-coefficient recurrence** (geometric C-finite, ratio `q`):
    `s(n+1) = q·s(n)` — the multiplicative-fold closing at rank 1. -/
def LinRec1 (q : Nat) (s : Nat → Nat) : Prop := ∀ n, s (n + 1) = q * s n

/-- A geometric sequence `c·bⁿ` is order-1 C-finite with ratio `b`. -/
theorem geom_linRec1 (c b : Nat) : LinRec1 b (fun k => c * b ^ k) := by
  intro n
  show c * b ^ (n + 1) = b * (c * b ^ n)
  rw [Nat.pow_succ, ← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm (c * b ^ n) b]

/-- A constant sequence is order-1 C-finite with ratio `1`. -/
theorem const_linRec1 (c : Nat) : LinRec1 1 (fun _ => c) := fun _ => (Nat.one_mul c).symm

/-- A constant sequence has finite difference-depth (depth `0`). -/
theorem const_reachesFloor (c : Nat) : reachesFloor (fun _ => c) := ⟨0, fun _ => rfl⟩

/-- ★★★ **The two fold-signatures are independent.**  Both the constant `1` and the geometric
    `2ⁿ` are **order-1** C-finite (multiplicative-fold rank 1), yet the constant has
    difference-depth `0` (`reachesFloor`) while `2ⁿ` has difference-depth `∞`
    (`¬ reachesFloor`).  So the multiplicative-fold order does not bound the additive-fold
    depth: they are independent finite signatures of a sequence. -/
theorem order_does_not_bound_depth :
    (LinRec1 1 (fun _ => (1 : Nat)) ∧ reachesFloor (fun _ => (1 : Nat)))
  ∧ (LinRec1 2 (fun k => 1 * 2 ^ k) ∧ ¬ reachesFloor (fun k => 1 * 2 ^ k)) :=
  ⟨⟨const_linRec1 1, const_reachesFloor 1⟩,
   ⟨geom_linRec1 1 2, geom_infinite_depth 1 2 (by decide) (by decide)⟩⟩

end E213.Lib.Math.Analysis.Cauchy.FoldSignatureSeparation
