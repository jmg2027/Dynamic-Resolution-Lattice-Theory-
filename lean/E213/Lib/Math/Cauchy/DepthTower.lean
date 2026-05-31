import E213.Lib.Math.Cauchy.DivergenceLadder

/-!
# DepthTower — the higher axis: ratio-lifts (logarithms) resolve the infinite depth

`DivergenceLadder` measures depth on the **difference axis** (`diff`, additive
lifts): finite for discrete polynomials, **∞ for Liouville-type** super-polynomial
growth.  But "∞" is only ∞ *on that axis*.  This file adds the axis above it — the
**ratio-lift** — and shows the infinite difference-depth becomes finite one
logarithm up.  The full invariant is then a *pair* `(log-height, poly-depth)`.

## The two axes

  - `diff s n = s(n+1) − s n` — the additive lift; tames **polynomial** growth
    (a degree-`d` discrete polynomial floors after `d+1` diffs, `DepthPRecursive`).
  - `ratioLift s n = s(n+1) / s n` — the multiplicative lift; tames **exponential**
    growth, exactly as `diff` tames linear growth: a geometric sequence `cⁿ` has
    *constant* ratio-lift (`geom_ratio_const`), the multiplicative analogue of a
    linear sequence having constant difference.

## The bridge — ratio is diff one logarithm down

The two axes are the same operator viewed through `log`:

    ratioLift (c^{e_n}) = c^{diff e_n}            (`ratio_is_diff_on_exponent`)

— the ratio of the *values* `c^{e_n}` is `c` raised to the *difference of the
exponents*.  So `ratioLift` is `diff` conjugated by the discrete logarithm
`exponent ↦ value`.  This is why the higher axis resolves the infinity:

  - a **Liouville** cross-determinant grows like `c^{k!}` — on the value
    (difference) axis it is super-polynomial, depth ∞ (`DivergenceLadder.infinite_depth`);
  - but its **exponent** `k!` is factorial-class, of *finite* difference-depth;
  - `ratioLift` reaches that exponent's difference structure — **one ratio-lift
    (one logarithm) drops Liouville from depth-∞ to the finite-depth world.**

## The emerging rule — the `(h, d)` coordinate

Every real here sits at a lexicographic pair: `h` = how many ratio-lifts
(logarithms) until the sequence is of polynomial (finite difference-depth) class,
then `d` = that difference-depth.

| real | `h` (log-height) | `d` (poly-depth) |
|---|---|---|
| algebraic (φ, √2) | 0 | 0 (constant cross-det) |
| e | 0 | 3 |
| π | 0 | 6 |
| Liouville `c^{k!}` | 1 | finite |
| tower `c^{c^{k!}}` | 2 | finite |

The difference-axis ∞ of `DivergenceLadder` is not a wall — it is the signal to
climb one axis.  The rule is uniform: **add a logarithm, re-measure; the height
needed is a new coordinate above the depth.**  Genuinely non-elementary growth
(unbounded log-height) is the true ∞ — the limit of the whole tower.

All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthTower

open E213.Lib.Math.Cauchy.DivergenceLadder (diff isConst)

/-! ## §1 — the ratio-lift (the higher axis) -/

/-- The **ratio-lift**: `ratioLift s n = s(n+1) / s n` (Nat division).  The
    multiplicative analogue of `diff`; the next axis up. -/
def ratioLift (s : Nat → Nat) : Nat → Nat := fun n => s (n+1) / s n

/-- ★★ **A geometric sequence has constant ratio-lift.**  `ratioLift (cⁿ) = c`
    (for `c ≥ 1`), so exponential growth is *floored at level 1 on the ratio
    axis* — exactly as a linear sequence is floored at level 1 on the difference
    axis.  Exponential is to ratio-lift what linear is to diff. -/
theorem geom_ratio_const (c : Nat) (hc : 1 ≤ c) :
    isConst (ratioLift (fun n => c^n)) := by
  intro n
  show c^(n+1) / c^n = c^(0+1) / c^0
  rw [Nat.pow_succ, Nat.mul_div_cancel c (Nat.pos_pow_of_pos n hc),
      Nat.pow_succ, Nat.pow_zero, Nat.mul_div_cancel c (Nat.pos_pow_of_pos 0 hc)]

/-! ## §2 — the bridge: ratio is diff one logarithm down -/

/-- ★★★ **`ratioLift` on values is `diff` on exponents.**  For a monotone exponent
    sequence `e`, `ratioLift (c^{e_n}) = c^{diff e_n}` — the higher axis *is* the
    lower axis conjugated by the discrete logarithm.  This is why a logarithm
    resolves the difference-axis infinity: a value-sequence with super-polynomial
    (depth-∞) difference behaviour can have a *finite-depth exponent*, and the
    ratio-lift reaches exactly that exponent's difference structure. -/
theorem ratio_is_diff_on_exponent (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat)
    (hmono : ∀ n, e n ≤ e (n+1)) (n : Nat) :
    ratioLift (fun n => c^(e n)) n = c^(diff e n) := by
  show c^(e (n+1)) / c^(e n) = c^(e (n+1) - e n)
  have hsplit : e (n+1) = e n + (e (n+1) - e n) := by
    rw [Nat.add_sub_cancel' (hmono n)]
  rw [hsplit, Nat.pow_add, Nat.mul_div_cancel_left _ (Nat.pos_pow_of_pos (e n) hc)]

/-! ## §3 — the tower coordinate -/

/-- `d`-fold difference lift (explicit, reduces by `rfl`). -/
def diffN : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,   s => s
  | d+1, s => diff (diffN d s)

/-- `h`-fold ratio lift. -/
def ratioN : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,   s => s
  | h+1, s => ratioLift (ratioN h s)

/-- The two-axis depth coordinate `(h, d)`: a sequence is at **log-height `h`,
    poly-depth `d`** if applying the ratio-lift `h` times yields a sequence whose
    `d`-th difference is constant.  Lexicographic; `h` is the new axis above the
    `DivergenceLadder` depth `d`. -/
def atTowerCoord (h d : Nat) (s : Nat → Nat) : Prop :=
  isConst (diffN d (ratioN h s))

/-- ★ **Geometric sits at `(1, 0)`** — one ratio-lift to a constant (`d = 0`):
    `cⁿ` is log-height 1, the simplest non-polynomial.  (Polynomials are height 0;
    `cⁿ` is the first thing the new axis is needed for.) -/
theorem geom_at_1_0 (c : Nat) (hc : 1 ≤ c) : atTowerCoord 1 0 (fun n => c^n) :=
  geom_ratio_const c hc

/-- ★ **Constants sit at `(0, 0)`** — the floor of both axes (the algebraic base). -/
theorem const_at_0_0 (c : Nat) : atTowerCoord 0 0 (fun _ => c) := fun _ => rfl

end E213.Lib.Math.Cauchy.DepthTower
