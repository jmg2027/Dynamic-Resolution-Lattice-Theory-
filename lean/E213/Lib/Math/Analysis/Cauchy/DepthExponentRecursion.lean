import E213.Lib.Math.Analysis.Cauchy.DepthTower

/-!
# DepthExponentRecursion — the third axis is recursion into the exponent

`DepthTower` gave two lift axes: `diff` (tames polynomial growth) and `ratioLift`
(tames a single exponential).  The honest correction recorded there: `ratioLift` is
a **difference on the exponent** (`ratio_is_diff_on_exponent`), so iterating it only
reaches `c^{polynomial}` — Liouville `c^{k!}` and the iterated exponentials lie
beyond.  The genuine extension is **not another `ratioLift`** but a recursion: to
resolve a value `c^{eₙ}`, resolve its *exponent sequence* `eₙ` — one axis down.

This file formalises that recursion.  With `expSeq c e n := c^{eₙ}`:

  * `ratioLift_expSeq` — one `ratioLift` peels one `diff` off the exponent:
    `ratioLift (expSeq c e) = expSeq c (diff e)` (the engine, = `ratio_is_diff_on_exponent`).
  * ★ `ratioN_expSeq` — iterating: `ratioN d (expSeq c e) = expSeq c (diffN d e)`
    (pointwise, no `funext`), for a *totally monotone* exponent (all iterated
    differences increasing).  **Resolving the value by `d` ratio-lifts = resolving
    the exponent by `d` differences.**
  * ★★★ `value_floors_iff_exponent_floors` — `expSeq c e` reaches its ratio-floor
    at depth `d` **iff** the exponent `e` reaches its diff-floor at depth `d`.  So
    the value lives exactly **one axis above its exponent**: its `ratio`-depth *is*
    the exponent's `diff`-depth.  This is the third axis made precise — the axis
    operator at each level is the same `(diff/ratio)` ladder, applied one exponent
    layer deeper.

So the tower of axes is a **self-similar recursion**, not a stack of new
primitives: `value-height = 1 + exponent-height`, bottoming out at a polynomial
(diff-resolvable) exponent.  Liouville `c^{k!}` is exactly the case where the
exponent `k!` is itself *not* diff-resolvable (factorial outgrows every polynomial),
so it needs the recursion one level deeper still — its exponent `k!` floors only
under *ratio* (`k! ↦ k+1`), i.e. `k!` is itself an `expSeq`-like object; the climb
that resolves it, recursing through exponent after exponent, is the frontier toward
`ε₀`.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthExponentRecursion

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff isConst)
open E213.Lib.Math.Analysis.Cauchy.DepthTower
  (ratioLift ratioN diffN ratio_is_diff_on_exponent)

/-- The value sequence `n ↦ c^{eₙ}` with exponent sequence `e`. -/
def expSeq (c : Nat) (e : Nat → Nat) : Nat → Nat := fun n => c ^ (e n)

/-- A **totally monotone** exponent: every iterated difference is increasing.
    (Factorial, polynomials, single exponentials all qualify; it is what lets the
    exponent recursion run without `Nat`-subtraction truncation.) -/
def totMono (e : Nat → Nat) : Prop := ∀ j n, (diffN j e) n ≤ (diffN j e) (n+1)

/-! ## §1 — the recursion engine -/

/-- ★ **One ratio-lift peels one difference off the exponent.**
    `ratioLift (expSeq c e) = expSeq c (diff e)` (pointwise). -/
theorem ratioLift_expSeq (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat)
    (hmono : ∀ n, e n ≤ e (n+1)) (n : Nat) :
    ratioLift (expSeq c e) n = expSeq c (diff e) n :=
  ratio_is_diff_on_exponent c hc e hmono n

/-- ★★★ **Iterated recursion**: `d` ratio-lifts of the value = `d` differences of
    the exponent — `ratioN d (expSeq c e) = expSeq c (diffN d e)` (pointwise).
    Resolving the value on the ratio axis *is* resolving the exponent on the diff
    axis, one layer down. -/
theorem ratioN_expSeq (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat) (htm : totMono e) :
    ∀ d n, ratioN d (expSeq c e) n = expSeq c (diffN d e) n := by
  intro d
  induction d with
  | zero => intro n; rfl
  | succ j ih =>
    intro n
    show ratioLift (ratioN j (expSeq c e)) n = expSeq c (diff (diffN j e)) n
    show (ratioN j (expSeq c e)) (n+1) / (ratioN j (expSeq c e)) n
       = c ^ (diff (diffN j e) n)
    rw [ih (n+1), ih n]
    exact ratio_is_diff_on_exponent c hc (diffN j e) (htm j) n

/-! ## §2 — value-height = exponent-height (one axis up) -/

/-- ★★★ **The value floors at ratio-depth `d` iff its exponent floors at diff-depth
    `d`.**  `c^{eₙ}` reaches its ratio-floor exactly when `eₙ` reaches its
    diff-floor — the value sits one axis above its exponent, and the recursion is
    the *same* ladder applied to the exponent.  (Both `isConst` here are pointwise,
    `= value at 0`.) -/
theorem value_floors_iff_exponent_floors (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat)
    (htm : totMono e) (d : Nat) :
    (∀ n, ratioN d (expSeq c e) n = ratioN d (expSeq c e) 0)
    ↔ (∀ n, c ^ (diffN d e n) = c ^ (diffN d e 0)) := by
  constructor
  · intro h n
    have := h n
    rw [ratioN_expSeq c hc e htm d n, ratioN_expSeq c hc e htm d 0] at this
    exact this
  · intro h n
    rw [ratioN_expSeq c hc e htm d n, ratioN_expSeq c hc e htm d 0]
    exact h n

/-- ★★ **Reduction**: if the exponent's `d`-th difference is constant, the value's
    `d`-th ratio-lift is constant — the value is resolved at ratio-depth `d`.  The
    forward engine of "value-height = exponent diff-depth". -/
theorem value_floor_of_exponent_floor (c : Nat) (hc : 1 ≤ c) (e : Nat → Nat)
    (htm : totMono e) (d : Nat) (hfloor : ∀ n, diffN d e n = diffN d e 0) :
    ∀ n, ratioN d (expSeq c e) n = ratioN d (expSeq c e) 0 := by
  intro n
  rw [ratioN_expSeq c hc e htm d n, ratioN_expSeq c hc e htm d 0]
  show c ^ (diffN d e n) = c ^ (diffN d e 0)
  rw [hfloor n]

end E213.Lib.Math.Analysis.Cauchy.DepthExponentRecursion
