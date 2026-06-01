import E213.Lib.Math.Real213.CrossDetOvertake
import E213.Meta.Tactic.NatHelper

/-!
# GeometricThreshold — the sharp growth-rate boundary for completability

`CrossDetOvertake` placed the completability boundary between two extremes over the
denominator `2^i`: a *constant* cross-determinant completes, a *double-exponential* one
breaks.  This file sharpens it to a **growth-rate threshold** over a general geometric
denominator `d_i = q^i` with a geometric cross-determinant `W_i = r^i`:

> `CrossDetSmall (r^·) (q^·)` holds (for all `i ≥ 1`) **iff the cross-determinant's
> growth rate is strictly below the denominator's**, `r < q`.

The threshold is `r < q`, i.e. `r + 1 ≤ q` — **not** `r ≤ q`.  The equal-rate case
`r = q` already *fails*: the polynomial factor `i(i+1)` on the cross-determinant side
is not absorbed by the single extra denominator factor `q` (the `q^{i+1}` headroom is
only linear-in-`q`, while the spoiler is linear-in-`i`).  So matching the denominator's
exponential rate is not enough; the cross-determinant must grow *strictly slower*.

  * ★ `succ_pow_ge` — the engine: `r^{n+1} + (n+1)·r^n ≤ (r+1)^{n+1}` (binomial first
    two terms), which inducts with no side condition and collapses the polynomial
    factor into the geometric gap.
  * ★★★ `geom_crossdet_small` — `r + 1 ≤ q ⟹ CrossDetSmall (r^·) (q^·)` for **all**
    `i ≥ 1` (no eventually-quantifier): below the rate threshold, free.
  * ★★★ `geom_crossdet_overtake` — `q^2 ≤ r ⟹ ¬ CrossDetSmall (r^·) (q^·)`: a strong
    overtake (rate at least the square) breaks it, via `overtake_breaks` at `i = 2`.
  * `geom_completability_boundary` — both sides bundled, the geometric analogue of
    `completability_boundary`.

The window `q < r < q^2` (overtake by a rate above `q` but below `q^2`) also fails, but
the failing index varies with `r/q`, so its clean single-statement falsifier needs a
per-`(r,q)` witness index rather than the fixed `i = 2`; `q^2 ≤ r` is the clean
immediately-provable complement to the sharp free side.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.GeometricThreshold

open E213.Lib.Math.Real213.CrossDetOvertake (CrossDetSmall overtake_breaks)
open E213.Tactic.NatHelper (mul_assoc add_mul)

/-- ★ **The polynomial-into-geometric engine.**  `r^{n+1} + (n+1)·r^n ≤ (r+1)^{n+1}` —
    the first two terms of the binomial expansion of `(r+1)^{n+1}`.  Inducts with no
    side condition; this is what lets the polynomial factor `(n+1)` be absorbed by one
    increment of the base. -/
theorem succ_pow_ge (r : Nat) : ∀ n, r ^ (n + 1) + (n + 1) * r ^ n ≤ (r + 1) ^ (n + 1)
  | 0 => by rw [Nat.pow_one, Nat.pow_zero, Nat.pow_one, Nat.one_mul]; exact Nat.le.refl
  | n + 1 => by
    have ih := succ_pow_ge r n
    have hstep : (r + 1) * (r ^ (n + 1) + (n + 1) * r ^ n) ≤ (r + 1) ^ (n + 2) := by
      rw [Nat.pow_succ (r+1) (n+1), Nat.mul_comm ((r+1)^(n+1)) (r+1)]
      exact Nat.mul_le_mul_left _ ih
    refine Nat.le_trans ?_ hstep
    have hPQ : r ^ (n + 1) = r * r ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    have hP2 : r ^ (n + 2) = r * r ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hP2, hPQ]
    generalize r ^ n = Q
    have hid : (r + 1) * (r * Q + (n + 1) * Q)
        = (r * (r * Q) + (n + 1 + 1) * (r * Q)) + (n + 1) * Q := by
      rw [Nat.mul_add, add_mul r 1 (r*Q), Nat.one_mul]
      rw [Nat.mul_comm (r+1) ((n+1)*Q), Nat.mul_add, Nat.mul_one]
      rw [Nat.succ_mul (n+1) (r*Q), mul_assoc (n+1) Q r, Nat.mul_comm Q r]
      rw [Nat.add_assoc, Nat.add_comm (r*Q) ((n+1)*(r*Q) + (n+1)*Q)]
      rw [Nat.add_assoc, Nat.add_comm ((n+1)*Q) (r*Q)]
      rw [← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc]
    rw [hid]; exact Nat.le_add_right _ _

/-- `(n+1)·r^n ≤ q^{n+1}` when `r + 1 ≤ q`: chain `succ_pow_ge` with base monotonicity. -/
theorem poly_le_geom {r q : Nat} (hrq : r + 1 ≤ q) (n : Nat) :
    (n + 1) * r ^ n ≤ q ^ (n + 1) :=
  Nat.le_trans (Nat.le_add_left _ _)
    (Nat.le_trans (succ_pow_ge r n) (Nat.pow_le_pow_left hrq (n + 1)))

/-- ★★★ **Below the rate threshold ⟹ free (all `i ≥ 1`).**  If the cross-determinant
    grows strictly slower than the denominator (`r + 1 ≤ q`), then
    `CrossDetSmall (r^·) (q^·)` holds for every `i ≥ 1` — no eventually-quantifier.
    By `CrossDetOvertake.crossdet_small_total_modulus` such a trajectory carries a free
    modulus. -/
theorem geom_crossdet_small {r q : Nat} (hrq : r + 1 ≤ q) :
    CrossDetSmall (fun i => r ^ i) (fun i => q ^ i) := by
  intro i hi
  match i, hi with
  | n + 1, _ =>
  show (n+1) * (n+1+1) * r ^ (n+1) + (n+1) * q ^ (n+1) ≤ (n+1+1) * q ^ (n+1+1)
  have key : (n + 1) * r ^ n ≤ q ^ (n + 1) := poly_le_geom hrq n
  have hr1 : r ^ (n+1) = r * r ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  have eL : (n+1) * (n+1+1) * (r * r ^ n) = (n+1+1) * (r * ((n+1) * r ^ n)) := by
    generalize n + 1 = a
    rw [Nat.mul_comm a (a+1), ← mul_assoc ((a+1)*a) r (r^n)]
    rw [← mul_assoc r a (r^n), Nat.mul_comm r a, mul_assoc a r (r^n)]
    rw [← mul_assoc (a+1) a (r*(r^n)), ← mul_assoc ((a+1)*a) r (r^n)]
  have term1 : (n+1) * (n+1+1) * r ^ (n+1) ≤ (n+1+1) * (r * q ^ (n+1)) := by
    rw [hr1, eL]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ key)
  have hcoef : (n+1+1) * r + (n+1) ≤ (n+1+1) * q := by
    have h0 : (n+1+1) * (r+1) ≤ (n+1+1) * q := Nat.mul_le_mul_left _ hrq
    rw [Nat.mul_add, Nat.mul_one] at h0
    exact Nat.le_trans (Nat.add_le_add_left (Nat.le_succ (n+1)) _) h0
  have hsum : (n+1+1) * (r * q ^ (n+1)) + (n+1) * q ^ (n+1) ≤ (n+1+1) * q ^ (n+1+1) := by
    calc (n+1+1) * (r * q ^ (n+1)) + (n+1) * q ^ (n+1)
        = ((n+1+1) * r) * q ^ (n+1) + (n+1) * q ^ (n+1) := by rw [mul_assoc]
      _ = ((n+1+1) * r + (n+1)) * q ^ (n+1) := (add_mul ((n+1+1)*r) (n+1) (q^(n+1))).symm
      _ ≤ ((n+1+1) * q) * q ^ (n+1) := Nat.mul_le_mul_right _ hcoef
      _ = (n+1+1) * q ^ (n+1+1) := by rw [mul_assoc, ← Nat.pow_succ']
  exact Nat.le_trans (Nat.add_le_add_right term1 _) hsum

/-- `q^{m+2} ≤ (q^2)^{m+1}` — a helper for the overtake side. -/
theorem q_pow_le {q : Nat} (m : Nat) : q ^ (m + 2) ≤ (q ^ 2) ^ (m + 1) := by
  induction m with
  | zero => rw [Nat.pow_one]; exact Nat.le.refl
  | succ k ih =>
    rw [Nat.pow_succ ((q^2)) (k+1), Nat.pow_succ q (k+2)]
    have hq : q ≤ q ^ 2 := by
      rcases Nat.eq_zero_or_pos q with h|h
      · subst h; rw [Nat.pow_two]; exact Nat.zero_le _
      · rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left q h
    exact Nat.mul_le_mul ih hq

/-- `q^{i+1} ≤ r^i` for `i ≥ 1` when `q^2 ≤ r` (the strong-overtake hypothesis). -/
theorem geom_overtake_pow {q r : Nat} (hr : q ^ 2 ≤ r) (i : Nat) (hi : 1 ≤ i) :
    q ^ (i + 1) ≤ r ^ i := by
  match i, hi with
  | m + 1, _ => exact Nat.le_trans (q_pow_le m) (Nat.pow_le_pow_left hr (m+1))

/-- ★★★ **Strong overtake ⟹ broken.**  If the cross-determinant's rate is at least the
    square of the denominator's (`q^2 ≤ r`), then `CrossDetSmall (r^·) (q^·)` fails —
    the overtake (`q^{i+1} ≤ r^i`) feeds `CrossDetOvertake.overtake_breaks` at `i = 2`. -/
theorem geom_crossdet_overtake {q r : Nat} (hq : 1 ≤ q) (hr : q ^ 2 ≤ r) :
    ¬ CrossDetSmall (fun i => r ^ i) (fun i => q ^ i) :=
  overtake_breaks (fun i => r ^ i) (fun i => q ^ i)
    (fun i => Nat.pos_pow_of_pos i hq)
    (fun i hi => geom_overtake_pow hr i (Nat.le_trans (by decide) hi))

/-- ★★★ **The sharp geometric completability boundary.**  Over the geometric
    denominator `q^i` (`q ≥ 2`): a cross-determinant growing strictly slower
    (`r + 1 ≤ q`) satisfies the smallness condition (free), while one growing at least
    as the square (`q^2 ≤ r'`) breaks it.  The completability boundary is a comparison
    of growth *rates*, with the threshold at `r < q` — matching the denominator's rate
    is not enough. -/
theorem geom_completability_boundary {q r r' : Nat} (hq : 2 ≤ q)
    (hsmall : r + 1 ≤ q) (hover : q ^ 2 ≤ r') :
    CrossDetSmall (fun i => r ^ i) (fun i => q ^ i)
      ∧ ¬ CrossDetSmall (fun i => r' ^ i) (fun i => q ^ i) :=
  ⟨geom_crossdet_small hsmall, geom_crossdet_overtake (Nat.le_trans (by decide) hq) hover⟩

end E213.Lib.Math.Real213.GeometricThreshold
