import E213.Lib.Math.Cauchy.DivergenceLadder
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PureNat

/-!
# DepthTower — the higher axis: ratio-lifts (logarithms) resolve the infinite depth

`DivergenceLadder` measures depth on the difference axis (`diff`, additive lifts):
finite for discrete polynomials, infinite for Liouville-type super-polynomial
growth.  But that infinity is infinity only on that axis.  This file adds the axis
above it — the ratio-lift — and shows the infinite difference-depth becomes finite
one logarithm up.  The full invariant is then a pair `(log-height, poly-depth)`.

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

Purity note: every Lean-core division-cancel (`Nat.mul_div_cancel{,_left}`,
`mul_div_right/left`, `mul_div_assoc`, `div_self`) pulls `propext`.  The PURE
division-cancel here is built from `Nat.div_eq_sub_div` (the one PURE division
primitive): `add_div_right_succ` → `mul_div_self_pure` → `mul_div_cancel_left_pure`.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthTower

open E213.Lib.Math.Cauchy.DivergenceLadder (diff isConst)

/-! ## §0 — PURE division-cancel (Lean-core div-cancel pulls propext) -/

/-- PURE `(x + b)/b = x/b + 1` (`b > 0`), from `Nat.div_eq_sub_div`. -/
private theorem add_div_right_succ (x b : Nat) (h : 0 < b) : (x+b)/b = x/b + 1 := by
  rw [Nat.div_eq_sub_div h (Nat.le_add_left b x),
      E213.Tactic.NatHelper.add_sub_cancel_right, Nat.add_comm]

/-- PURE `k*b/b = k` (`b > 0`), by induction on `k`. -/
private theorem mul_div_self_pure (k b : Nat) (h : 0 < b) : k*b/b = k := by
  induction k with
  | zero => rw [Nat.zero_mul]; exact Nat.zero_div b
  | succ j ih => rw [Nat.succ_mul, add_div_right_succ (j*b) b h, ih]

/-- PURE left-cancel `a*b/a = b` (`a > 0`), via `mul_div_self_pure` + commute. -/
private theorem mul_div_cancel_left_pure (a b : Nat) (h : 0 < a) : a*b/a = b := by
  rw [Nat.mul_comm a b]; exact mul_div_self_pure b a h

/-- PURE `c^(a+b) = c^a * c^b` (Lean-core `Nat.pow_add` pulls `propext`). -/
private theorem pow_add_pure (c a b : Nat) : c^(a+b) = c^a * c^b := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ j ih =>
    rw [show a+(j+1) = (a+j)+1 from rfl, Nat.pow_succ, ih, Nat.pow_succ]
    exact E213.Meta.Nat.PureNat.mul_assoc (c^a) (c^j) c

/-! ## §1 — the ratio-lift (the higher axis) -/

/-- The ratio-lift: `ratioLift s n = s(n+1) / s n` (Nat division).  The
    multiplicative analogue of `diff`; the next axis up. -/
def ratioLift (s : Nat → Nat) : Nat → Nat := fun n => s (n+1) / s n

/-- `c^(n+1) / c^n = c` for `c ≥ 1`. -/
private theorem pow_succ_div (c n : Nat) (hc : 1 ≤ c) : c^(n+1) / c^n = c := by
  rw [Nat.pow_succ]
  exact mul_div_cancel_left_pure (c^n) c (Nat.pos_pow_of_pos n hc)

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
    rw [← pow_add_pure, E213.Tactic.NatHelper.add_sub_of_le (hmono n)]
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

end E213.Lib.Math.Cauchy.DepthTower
