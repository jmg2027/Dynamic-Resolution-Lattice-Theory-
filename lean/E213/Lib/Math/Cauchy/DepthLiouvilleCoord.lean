import E213.Lib.Math.Cauchy.DepthTower
import E213.Meta.Nat.NatDiv213

/-!
# DepthLiouvilleCoord — Liouville's exponent gets a coordinate one recursion tier down

`DivergenceLadder.infinite_depth` and `DepthDoubleExp.dexp_not_const` place the
Liouville cross-determinant `c^{k!}` **outside** the finite `(h, d)` reach: its
exponent `k!` is super-polynomial, so neither the difference axis nor the ratio axis
ever floors the value.  On the two value-axes, `c^{k!}` has no finite coordinate.

But `DepthExponentRecursion` gave a genuinely new operation — recurse into the
exponent — and on *that* axis the Liouville exponent is not pathological.  This file
gives `k!` its coordinate there:

  * ★ `ratioLift_fact` — the factorial's ratio-lift is the **linear** sequence:
    `ratioLift fact n = (n+1)!/n! = n+1`.  A single ratio sends the super-polynomial
    `k!` to the degree-1 object `k+1` — "the exponent is itself an `expSeq`-like
    object, resolved by ratio".
  * ★★ `diff_ratioLift_fact` — one further difference floors it: `Δ(n+1) = 1`,
    constant.  So `k!` reaches its floor under **ratio-then-diff** — a finite
    coordinate on the exponent recursion, even though (`diff_fact`: `Δ(k!) = k·k!`)
    it never floors on the difference axis alone.

So the Liouville value `c^{k!}`, with *no* finite `(h, d)`, acquires a finite
coordinate once the recursion descends into its exponent: the exponent `k!` lives at
ratio-depth `1`, diff-depth `1`, and the value sits one recursion tier above it.
This is the climb `DepthExponentRecursion`/`DepthOmegaTower` described — resolving an
exponent that is itself resolved by the ladder — the frontier toward `ε₀`, made
concrete on the factorial.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthLiouvilleCoord

open E213.Lib.Math.Cauchy.DivergenceLadder (diff)
open E213.Lib.Math.Cauchy.DepthTower (ratioLift ratio_is_diff_on_exponent)
open E213.Meta.Nat.NatDiv213 (mul_div_self_pure)
open E213.Tactic.NatHelper (succ_sub add_sub_cancel_right)

/-! ## §1 — the factorial (213-native; Lean-core `Nat.factorial` lives in Mathlib) -/

/-- The factorial sequence `n ↦ n!` — the Liouville cross-determinant's exponent. -/
def fact : Nat → Nat
  | 0   => 1
  | n+1 => (n+1) * fact n

/-- `(n+1)! = (n+1)·n!` (definitional). -/
theorem fact_succ (n : Nat) : fact (n+1) = (n+1) * fact n := rfl

/-- `0 < n!` for every `n`. -/
theorem fact_pos : ∀ n, 0 < fact n
  | 0   => Nat.one_pos
  | n+1 => by rw [fact_succ]; exact Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- `n!` is monotone — its exponent recursion runs without `Nat`-subtraction
    truncation. -/
theorem fact_mono (n : Nat) : fact n ≤ fact (n+1) := by
  rw [fact_succ]; exact Nat.le_mul_of_pos_left (fact n) (Nat.succ_pos n)

/-! ## §2 — the factorial's exponent coordinate: ratio-then-diff -/

/-- ★ **The factorial's ratio-lift is linear.**  `ratioLift fact n = (n+1)!/n! =
    n+1`: a single ratio collapses the super-polynomial `k!` to the degree-1
    sequence `k+1`.  The Liouville exponent is itself resolved by the ratio axis one
    tier down.  (PURE division-cancel via `mul_div_self_pure`.) -/
theorem ratioLift_fact (n : Nat) : ratioLift fact n = n + 1 := by
  show fact (n+1) / fact n = n + 1
  rw [fact_succ]
  exact mul_div_self_pure (n+1) (fact n) (fact_pos n)

/-- ★★ **One further difference floors the factorial's ratio.**  `Δ(ratioLift fact)
    n = (n+2) − (n+1) = 1`, constant — so `k!` reaches its floor under
    *ratio-then-diff*: a finite coordinate (ratio-depth 1, diff-depth 1) on the
    exponent recursion. -/
theorem diff_ratioLift_fact (n : Nat) : diff (ratioLift fact) n = 1 := by
  show ratioLift fact (n+1) - ratioLift fact n = 1
  rw [ratioLift_fact (n+1), ratioLift_fact n]
  exact succ_sub (n+1)

/-- The factorial **never** floors on the difference axis alone: `Δ(k!) = (n+1)! −
    n! = (n+1)·n! − n! = n·n!`, still super-polynomial.  This is why the Liouville
    value has no finite `(h, d)` — the resolution must recurse into the exponent
    (§2), not iterate the value-axes. -/
theorem diff_fact (n : Nat) : diff fact n = n * fact n := by
  show fact (n+1) - fact n = n * fact n
  rw [fact_succ, Nat.succ_mul]
  exact add_sub_cancel_right (n * fact n) (fact n)

/-! ## §3 — the value side: `c^{k!}` and the exponent it must recurse into -/

/-- One value-ratio peels one difference off the exponent of `c^{k!}`:
    `ratioLift (n ↦ c^{n!}) n = c^{Δ(k!) n} = c^{n·n!}`.  The exponent of the value's
    ratio is *still growing* (`diff_fact`), so the value never floors on the ratio
    axis — confirming `c^{k!}` has no finite `(h, d)`; its resolution is the
    exponent recursion of §2, not the value axis. -/
theorem ratioLift_factExp (c : Nat) (hc : 1 ≤ c) (n : Nat) :
    ratioLift (fun n => c ^ (fact n)) n = c ^ (diff fact n) :=
  ratio_is_diff_on_exponent c hc fact fact_mono n

/-- ★★★ **Liouville's recursion coordinate.**  The cross-determinant exponent `k!`
    of a Liouville number has no finite difference-depth (`diff_fact`: `Δ(k!) =
    k·k!`, super-polynomial), so the value `c^{k!}` has no finite `(h, d)` on the two
    value-axes.  Yet `k!` acquires a finite coordinate on the *exponent recursion*: a
    single ratio sends `k! ↦ k+1` (`ratioLift_fact`), and one further difference
    floors it to the constant `1` (`diff_ratioLift_fact`).  The exponent is itself
    resolved by the `(ratio, diff)` ladder one tier down; the value `c^{k!}` sits one
    recursion level above it — the concrete frontier climbing toward `ε₀`. -/
theorem liouville_exponent_coordinate :
    (∀ n, ratioLift fact n = n + 1)
    ∧ (∀ n, diff (ratioLift fact) n = 1)
    ∧ (∀ n, diff fact n = n * fact n) :=
  ⟨ratioLift_fact, diff_ratioLift_fact, diff_fact⟩

end E213.Lib.Math.Cauchy.DepthLiouvilleCoord
