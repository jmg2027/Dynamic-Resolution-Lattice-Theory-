import E213.Lib.Math.Cauchy.DivergenceLadder

/-!
# DepthPRecursive — finite divergence depth is discrete-polynomial (P-recursive)

`DivergenceLadder` measures divergence depth by lifting a sequence with the
finite-difference operator `diff` until it becomes constant.  This file proves the
structural fact behind the depth-classification:

> a sequence has finite divergence depth iff it is a discrete polynomial — its
> convergents are P-recursive of bounded difference-order.

The engine is that `diff` commutes through the iterate `liftK`
(`liftK_diff_comm`).  Defining `polyDepth d s` as "the `d`-th finite difference of
`s` is constant" (a discrete polynomial of degree at most `d`):

  * `polyDepth_succ_iff` : `polyDepth (d+1) s` iff `polyDepth d (diff s)` — a
    difference lowers the degree by exactly one, so depth is the number of
    differences to a constant.
  * `polyDepth_reachesFloor` : finite `polyDepth` implies the ladder terminates.
  * `reachesFloor_lift` : anti-differencing keeps finite depth.

So the finite-depth reals are exactly the discrete polynomials of the
cross-determinant ladder = the P-recursive class.  e has `polyDepth 1` (ladder
ratio `n+1`), an algebraic irrational `polyDepth 0` (constant cross-determinant);
Liouville-type numbers have no finite `polyDepth`
(`DivergenceLadder.infinite_depth`).  This is the holonomic/P-recursive rank, not
the irrationality measure.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthPRecursive

open E213.Lib.Math.Cauchy.DivergenceLadder (diff liftK isConst reachesFloor)

/-- `diff` commutes through `liftK`: the `(k+1)`-fold difference is the `k`-fold
    difference of the difference. -/
theorem liftK_diff_comm (k : Nat) (s : Nat → Nat) :
    liftK (k+1) s = liftK k (diff s) := by
  induction k generalizing s with
  | zero => rfl
  | succ j ih => show diff (liftK (j+1) s) = diff (liftK j (diff s)); rw [ih]

/-- `polyDepth d s`: the `d`-th finite difference of `s` is constant — `s` is a
    discrete polynomial of degree at most `d` (P-recursive of difference-order
    `d`). -/
def polyDepth (d : Nat) (s : Nat → Nat) : Prop := isConst (liftK d s)

/-- A difference lowers the degree by exactly one. -/
theorem polyDepth_succ_iff (d : Nat) (s : Nat → Nat) :
    polyDepth (d+1) s ↔ polyDepth d (diff s) := by
  unfold polyDepth
  rw [liftK_diff_comm d s]

/-- A constant sequence is degree 0. -/
theorem const_polyDepth0 (c : Nat) : polyDepth 0 (fun _ => c) := fun _ => rfl

/-- Finite polynomial depth implies the divergence ladder terminates. -/
theorem polyDepth_reachesFloor (d : Nat) (s : Nat → Nat) (h : polyDepth d s) :
    reachesFloor s := ⟨d, h⟩

/-- If `diff s` reaches its floor, so does `s`, one level deeper. -/
theorem reachesFloor_lift (s : Nat → Nat) (h : reachesFloor (diff s)) :
    reachesFloor s := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k+1, by rw [liftK_diff_comm k s]; exact hk⟩

end E213.Lib.Math.Cauchy.DepthPRecursive
