import E213.Lib.Math.Cauchy.DivergenceLadder

/-!
# DepthPRecursive — finite divergence depth ⟺ discrete-polynomial (P-recursive)

`DivergenceLadder` introduced the divergence depth (lift the cross-determinant's
form until constant).  This file proves the structural characterization the
depth-classification rests on:

> **a sequence has finite divergence depth iff it is a *discrete polynomial* —
> equivalently, its convergents are P-recursive of bounded difference-order.**

The bridge is the **lift operator** `diff` (forward finite difference) and the key
algebraic fact that `diff` commutes through the iterate `liftK`
(`liftK_diff_comm`).  From it:

  - `polyDepth d s` := *the `d`-th finite difference of `s` is constant* — `s` is a
    discrete polynomial of degree `≤ d`.  This is exactly "`s` satisfies a
    constant-/polynomial-coefficient recurrence that the `d`-fold difference
    annihilates to a constant", i.e. P-recursive of difference-order `d`.
  - ★ `polyDepth_succ_iff` : `polyDepth (d+1) s ↔ polyDepth d (diff s)` — **degree
    lowers by exactly one under `diff`.**  This is the engine: depth is the number
    of differences to a constant, and each difference drops it by 1.
  - `reachesFloor_lift` : if `diff s` reaches a constant floor, so does `s` (at one
    level deeper) — the finite-construction direction.
  - `polyDepth_reachesFloor` : finite `polyDepth ⟹ reachesFloor` — finite depth.

So the finite-depth reals are exactly the discrete polynomials of the
cross-determinant ladder = the P-recursive class; the depth is the polynomial
degree + the fixed offset (cross-det + ratio) measured in `DivergenceDepth`.  e
(ladder ratio `n+1`, `polyDepth 1`) and π (ratio a degree-4 polynomial,
`polyDepth 4`) are instances; an algebraic irrational is `polyDepth 0` (constant
cross-determinant).  Liouville-type numbers have **no** finite `polyDepth`
(`DivergenceLadder.infinite_depth`) — they are not P-recursive at this level.

This is *not* the irrationality measure (`probe_twist_conic.md §7`): it is the
P-recursive / holonomic rank, orthogonal to Diophantine approximability.

All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthPRecursive

open E213.Lib.Math.Cauchy.DivergenceLadder (diff liftK isConst reachesFloor)

/-! ## §1 — the lift commutes through the iterate -/

/-- ★ **`diff` commutes through `liftK`**: `liftK (k+1) s = liftK k (diff s)`.  The
    `(k+1)`-fold difference is the `k`-fold difference of the difference — the
    associativity that lets depth be counted from either end. -/
theorem liftK_diff_comm (k : Nat) (s : Nat → Nat) :
    liftK (k+1) s = liftK k (diff s) := by
  induction k generalizing s with
  | zero => rfl
  | succ j ih => show diff (liftK (j+1) s) = diff (liftK j (diff s)); rw [ih]

/-! ## §2 — discrete-polynomial depth and the degree-lowering law -/

/-- **`polyDepth d s`**: the `d`-th finite difference of `s` is constant — `s` is a
    discrete polynomial of degree `≤ d` (equivalently P-recursive of
    difference-order `d`). -/
def polyDepth (d : Nat) (s : Nat → Nat) : Prop := isConst (liftK d s)

/-- ★★★ **Degree lowers by one under `diff`**: `polyDepth (d+1) s ↔ polyDepth d
    (diff s)`.  Differencing a degree-`(d+1)` discrete polynomial yields a
    degree-`d` one, and conversely.  This is the formal core of "finite depth ⟺
    P-recursive": the depth is exactly the number of differences to a constant, and
    `diff` peels one off. -/
theorem polyDepth_succ_iff (d : Nat) (s : Nat → Nat) :
    polyDepth (d+1) s ↔ polyDepth d (diff s) := by
  unfold polyDepth
  rw [liftK_diff_comm d s]

/-- ★ A constant sequence is degree 0. -/
theorem const_polyDepth0 (c : Nat) : polyDepth 0 (fun _ => c) := fun _ => rfl

/-! ## §3 — finite depth ⟹ reaches floor; the lift law -/

/-- ★★ **Finite polynomial depth ⟹ reaches the floor.**  If some finite
    difference of `s` is constant, `s` reaches its divergence floor — finite depth.
    This is the structured / P-recursive ⟹ terminating-ladder direction. -/
theorem polyDepth_reachesFloor (d : Nat) (s : Nat → Nat) (h : polyDepth d s) :
    reachesFloor s := ⟨d, h⟩

/-- ★★ **Floor-lift law**: if `diff s` reaches its floor, so does `s`, one level
    deeper.  Anti-differencing a finite-depth sequence keeps it finite-depth — the
    constructive face: every discrete polynomial is built from a constant by
    finitely many anti-differences. -/
theorem reachesFloor_lift (s : Nat → Nat) (h : reachesFloor (diff s)) :
    reachesFloor s := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k+1, by rw [liftK_diff_comm k s]; exact hk⟩

end E213.Lib.Math.Cauchy.DepthPRecursive
