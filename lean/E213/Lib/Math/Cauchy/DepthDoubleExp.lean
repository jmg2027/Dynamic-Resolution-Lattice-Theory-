import E213.Lib.Math.Cauchy.DepthExponentRecursion
import E213.Meta.Tactic.NatHelper

/-!
# DepthDoubleExp — the second axis cannot reach the second exponent layer

`DepthExponentRecursion` showed the axis tower is a self-similar recursion: a value
`c^{eₙ}` is resolved by recursing into its exponent `eₙ`.  This file proves the
*negative* fact that forces the recursion to be genuinely new at each layer — and
corrects the earlier mistaken reading that iterating `ratioLift` climbs the tower.

**The single-ratio axis `ratioN` reaches exactly `c^{polynomial}`, not the second
exponential layer.**  Concretely, the double exponential `2^{2ⁿ}` is a **fixed
point** of `ratioLift`: no number of ratio-lifts ever floors it.

The witness is that `2ⁿ` is a fixed point of `diff` (`diff_twoPow`: `Δ(2ⁿ) = 2ⁿ`),
hence of every iterated difference (`diffN_twoPow`: `diffN h (2ⁿ) = 2ⁿ`).  Through
the recursion bridge `ratioN_expSeq` (`ratioN h (c^{eₙ}) = c^{diffN h eₙ}`), this
gives `ratioN h (2^{2ⁿ}) = 2^{2ⁿ}` for *every* `h` (`ratioN_dexp`) — the value never
simplifies — so it never reaches a constant floor (`dexp_not_const`).

So the reach of the two-operator system `(ratioN, diffN)` is *exactly* `c^{poly}`
(coordinate `(h, d)` with `h` = exponent's polynomial degree, `< ω²`).  The second
exponential layer `c^{c^{poly}}` lies **strictly beyond** it: reaching it needs the
*recursion* of `DepthExponentRecursion` (apply the whole `(ratio, diff)` ladder to
the exponent), a genuinely new operation, not a longer run of `ratioLift`.

Consequence for the ordinal picture.  Each exponential layer is a new axis, and —
under the recursion — multiplies the rank by `ω` (a value's resolution depth is the
exponent's depth lifted one full axis).  So a depth-`r` finite tower of exponentials
sits at rank `ω^r · d`, the finite-`r` supremum is `ω^ω`, and reaching `ε₀` requires
diagonalising the tower *height* itself — a further meta-recursion.  **`ε₀` is not
"the end" of the axes; it is the closure of one diagonalisation, with `ε₀ + 1`,
`ε₁`, … above.**  This file pins the first non-trivial step (`ratioN` cannot cross
one exponential layer) ∅-axiom; the `ω^ω`/`ε₀` reading is the classical ordinal
interpretation of these sequence facts.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthDoubleExp

open E213.Lib.Math.Cauchy.DepthExponentRecursion (expSeq totMono ratioN_expSeq)
open E213.Lib.Math.Cauchy.DivergenceLadder (diff)
open E213.Lib.Math.Cauchy.DepthTower (ratioN diffN)

/-- The exponent sequence `n ↦ 2ⁿ` (so `expSeq 2 twoPow` is the double exponential
    `n ↦ 2^{2ⁿ}`). -/
def twoPow : Nat → Nat := fun n => 2^n

/-! ## §1 — `2ⁿ` is a fixed point of the difference operator -/

/-- ★ `Δ(2ⁿ) = 2ⁿ` — the exponential is its own difference. -/
theorem diff_twoPow (n : Nat) : diff twoPow n = twoPow n := by
  show 2^(n+1) - 2^n = 2^n
  rw [Nat.pow_succ, Nat.mul_two, E213.Tactic.NatHelper.add_sub_cancel_right]

/-- ★★ Every iterated difference fixes `2ⁿ`: `diffN h (2ⁿ) = 2ⁿ`.  So `2ⁿ` never
    floors under `diff` — it is super-polynomial. -/
theorem diffN_twoPow (h : Nat) : ∀ n, diffN h twoPow n = twoPow n := by
  induction h with
  | zero => intro n; rfl
  | succ j ih =>
    intro n
    show (diffN j twoPow) (n+1) - (diffN j twoPow) n = twoPow n
    rw [ih (n+1), ih n]; exact diff_twoPow n

/-- `twoPow` is totally monotone (each iterated difference, being `2ⁿ`, increases). -/
theorem twoPow_totMono : totMono twoPow := by
  intro j n
  rw [diffN_twoPow j n, diffN_twoPow j (n+1)]
  show 2^n ≤ 2^(n+1)
  rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_right (2^n) (by decide)

/-! ## §2 — the double exponential is a fixed point of every `ratioN` -/

/-- ★★★ **`ratioN h` fixes the double exponential**: `ratioN h (2^{2ⁿ}) = 2^{2ⁿ}`
    for every `h`.  Via the recursion bridge `ratioN_expSeq` (`ratioN h (c^{eₙ}) =
    c^{diffN h eₙ}`) and `diffN_twoPow` (`diffN h (2ⁿ) = 2ⁿ`): the ratio axis does a
    difference *on the exponent*, but `2ⁿ` is fixed by differences, so the value
    never changes. -/
theorem ratioN_dexp (h n : Nat) :
    ratioN h (expSeq 2 twoPow) n = expSeq 2 twoPow n := by
  rw [ratioN_expSeq 2 (by decide) twoPow twoPow_totMono h n]
  show 2^(diffN h twoPow n) = 2^(twoPow n)
  rw [diffN_twoPow h n]

/-- ★★★ **The double exponential never floors under `ratioN`.**  For every depth
    `h`, `ratioN h (2^{2ⁿ})` is *not* constant (it equals `2^{2ⁿ}`, which already
    differs at `n = 0, 1`: `2 ≠ 4`).  So `c^{c^{poly}}` has **no** finite `(h,d)`
    coordinate — the single-ratio axis cannot cross one exponential layer; the
    second layer needs the genuine recursion of `DepthExponentRecursion`. -/
theorem dexp_not_const (h : Nat) :
    ¬ (∀ n, ratioN h (expSeq 2 twoPow) n = ratioN h (expSeq 2 twoPow) 0) := by
  intro hc
  have h1 := hc 1
  rw [ratioN_dexp h 1, ratioN_dexp h 0] at h1
  exact absurd h1 (by decide)

end E213.Lib.Math.Cauchy.DepthDoubleExp
