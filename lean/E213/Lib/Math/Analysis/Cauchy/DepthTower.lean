import E213.Lib.Math.Analysis.Cauchy.DivergenceLadder
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PureNat
import E213.Meta.Nat.NatDiv213

/-!
# DepthTower — the higher axis: ratio-lifts resolve growth one exponent layer down

`DivergenceLadder` measures depth on the difference axis (`diff`, additive lifts):
finite for discrete polynomials, infinite for super-polynomial growth.  But that
infinity is infinity only on that axis.  This file adds the axis above it — the
ratio-lift — which differences the exponent: `ratioLift (c^{eₙ}) = c^{diff eₙ}`, so
`ratioLift^h` floors exactly `c^{polynomial of degree h}`.  The full invariant is a
pair `(h, d)` with `h` the exponent's polynomial degree, `d` the residual
difference-depth.

## The two axes

  * `diff s n = s(n+1) - s n` — the additive lift; tames polynomial growth.
  * `ratioLift s n = s(n+1) / s n` — the multiplicative lift; tames exponential
    growth, exactly as `diff` tames linear growth: a geometric sequence `cⁿ` has
    constant ratio-lift (`geom_ratio_const`), the multiplicative analogue of a
    linear sequence having constant difference.

## The bridge — ratio is a difference *on the exponent*

The second axis is the first one applied to the exponent:

    ratioLift (c^{e n}) = c^{diff e n}            (`ratio_is_diff_on_exponent`)

— the ratio of the values `c^{e n}` is `c` raised to the *difference of the
exponents*.  So `ratioLift^h` floors exactly `c^{polynomial of degree h}`: the
coordinate `h` is the **exponent's polynomial degree**.

Scope (honest).  Because `ratioLift` only *differences* the exponent, this captures
exactly the `c^{poly}` reals — single exponentials with polynomial exponent.  A
Liouville cross-determinant `c^{k!}` is *not* in reach: `k!` is super-polynomial, so
`ratioLift` sends `c^{k!} ↦ c^{diff k!} = c^{k!·k}` (exponent still growing) and
never floors.  The genuine extension is **not** another `ratioLift`; it is a *ratio
on the exponent* — apply the whole `(ratio, diff)` ladder to the exponent sequence
itself (the exponent `k!` floors under ratio: `k! ↦ k+1`).  That self-similar
recursion (ladder-on-the-exponent, then on its exponent, …) is the third and higher
axes; this file proves only the first two and the `(h,d)` coordinate.

## The coordinate `(h, d)`

`h` = ratio-lifts (= exponent polynomial degree) until `c^{poly}` class, then `d` =
difference-depth.  algebraic `(0,0)` · `cⁿ` (exponent degree 1) `(1,0)` · `c^{n²}`
`(2,0)`.  e and π and the Liouville/iterated-exponential reals lie *beyond* finite
`(h,d)` and need the exponent-recursion above.

Purity note: every Lean-core division-cancel pulls `propext`.  The PURE
division-cancel chain (`mul_div_self_pure`, `mul_div_cancel_left_pure`,
`pow_succ_div`) lives in `E213.Meta.Nat.NatDiv213`; `pow_add` in
`E213.Meta.Nat.PureNat`.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthTower

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff isConst)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure pow_succ_div)
open E213.Meta.Nat.PureNat (pow_add)

/-! ## §1 — the ratio-lift (the higher axis) -/

/-- The ratio-lift: `ratioLift s n = s(n+1) / s n` (Nat division).  The
    multiplicative analogue of `diff`; the next axis up. -/
def ratioLift (s : Nat → Nat) : Nat → Nat := fun n => s (n+1) / s n

/-- A geometric sequence has constant ratio-lift: `ratioLift (cⁿ) = c` (for
    `c ≥ 1`).  Exponential growth is floored at level 1 on the ratio axis, exactly
    as a linear sequence is floored at level 1 on the difference axis. -/
theorem geom_ratio_const (c : Nat) (hc : 1 ≤ c) :
    isConst (ratioLift (fun n => c^n)) := by
  intro n
  show c^(n+1) / c^n = c^(0+1) / c^0
  rw [pow_succ_div c n hc, pow_succ_div c 0 hc]

/-! ## §2 — the bridge: ratio is diff one logarithm down -/

/-- `ratioLift` on values is `diff` on exponents.  For a monotone exponent sequence
    `e`, `ratioLift (c^{e n}) = c^{diff e n}` — the higher axis is the lower axis
    conjugated by the discrete logarithm.  A value-sequence with super-polynomial
    (infinite-depth) difference behaviour can have a finite-depth exponent, and the
    ratio-lift reaches exactly that exponent's difference structure. -/
theorem ratio_is_diff_on_exponent (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat)
    (hmono : ∀ n, e n ≤ e (n+1)) (n : Nat) :
    ratioLift (fun n => c^(e n)) n = c^(diff e n) := by
  show c^(e (n+1)) / c^(e n) = c^(e (n+1) - e n)
  have hpow : c^(e (n+1)) = c^(e n) * c^(e (n+1) - e n) := by
    rw [← pow_add, E213.Tactic.NatHelper.add_sub_of_le (hmono n)]
  rw [hpow]
  exact mul_div_cancel_left_pure (c^(e n)) (c^(e (n+1) - e n)) (Nat.pos_pow_of_pos (e n) hc)

/-! ## §3 — the tower coordinate -/

/-- `d`-fold difference lift. -/
def diffN : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,   s => s
  | d+1, s => diff (diffN d s)

/-- `h`-fold ratio lift. -/
def ratioN : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,   s => s
  | h+1, s => ratioLift (ratioN h s)

/-- The two-axis depth coordinate `(h, d)`: a sequence is at log-height `h`,
    poly-depth `d` if applying the ratio-lift `h` times yields a sequence whose
    `d`-th difference is constant.  `h` is the axis above the `DivergenceLadder`
    depth `d`. -/
def atTowerCoord (h d : Nat) (s : Nat → Nat) : Prop :=
  isConst (diffN d (ratioN h s))

/-- A geometric sequence sits at `(1, 0)` — one ratio-lift to a constant: `cⁿ` is
    log-height 1, the simplest non-polynomial. -/
theorem geom_at_1_0 (c : Nat) (hc : 1 ≤ c) : atTowerCoord 1 0 (fun n => c^n) :=
  geom_ratio_const c hc

/-- A constant sits at `(0, 0)` — the floor of both axes (the algebraic base). -/
theorem const_at_0_0 (c : Nat) : atTowerCoord 0 0 (fun _ => c) := fun _ => rfl

end E213.Lib.Math.Analysis.Cauchy.DepthTower
