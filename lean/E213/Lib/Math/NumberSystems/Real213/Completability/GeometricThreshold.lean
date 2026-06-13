import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetOvertake
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
  * ★★★ `geom_crossdet_overtake_sharp` — `q ≤ r ⟹ ¬ CrossDetSmall (r^·) (q^·)`: at or
    above the denominator's rate it breaks, tested at the single fixed witness index
    `i = q` (no overtake lemma, no `q^2` machinery — covers the equal-rate case `r = q`
    and everything above).
  * ★★★ `geom_boundary_iff` — the exact boundary: `CrossDetSmall (r^·) (q^·) ↔ r < q`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.GeometricThreshold

open E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake (CrossDetSmall)
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

/-- `q·(q+1) + q = q·(q+2)` — the cross-determinant-side collapse at the witness
    index `i = q`. -/
theorem q_collapse (q : Nat) : q * (q + 1) + q = q * (q + 2) := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  rw [Nat.add_assoc, show q + q = 2 * q from (Nat.two_mul q).symm]
  rw [show q * 2 = 2 * q from Nat.mul_comm q 2]

/-- ★★★ **At or above the denominator's rate ⟹ broken.**  For `q ≥ 2` and `q ≤ r`,
    `CrossDetSmall (r^·) (q^·)` fails — tested at the single fixed witness index
    `i = q`: smallness would force `q(q+2)·q^q ≤ q(q+1)·q^q` (LHS via `r^q ≥ q^q` and
    the collapse `q(q+1)+q = q(q+2)`; RHS via `(q+1)q^{q+1} = q(q+1)q^q`), contradicting
    `q(q+1) < q(q+2)`.  Needs only `q ≤ r` — covering the equal-rate case `r = q` and the
    whole window up to the strong overtake, with no overtake lemma. -/
theorem geom_crossdet_overtake_sharp {q r : Nat} (hq : 2 ≤ q) (hrq : q ≤ r) :
    ¬ CrossDetSmall (fun i => r ^ i) (fun i => q ^ i) := by
  intro hcs
  have hq1 : 1 ≤ q := Nat.le_trans (by decide) hq
  have hsmall : q * (q + 1) * r ^ q + q * q ^ q ≤ (q + 1) * q ^ (q + 1) := hcs q hq1
  have hrq_pow : q ^ q ≤ r ^ q := Nat.pow_le_pow_left hrq q
  have hLB : q * (q + 1) * q ^ q + q * q ^ q ≤ q * (q + 1) * r ^ q + q * q ^ q :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ hrq_pow) _
  have hcollapse : q * (q + 1) * q ^ q + q * q ^ q = q * (q + 2) * q ^ q := by
    rw [← add_mul, q_collapse]
  have hRHS : (q + 1) * q ^ (q + 1) = q * (q + 1) * q ^ q := by
    rw [Nat.pow_succ, Nat.mul_comm (q^q) q, mul_assoc q (q+1) (q^q),
        Nat.mul_comm (q+1) (q * q^q), mul_assoc q (q^q) (q+1),
        Nat.mul_comm (q^q) (q+1), ← mul_assoc q (q+1) (q^q)]
  have hchain : q * (q + 2) * q ^ q ≤ q * (q + 1) * q ^ q :=
    calc q * (q + 2) * q ^ q
        = q * (q + 1) * q ^ q + q * q ^ q := hcollapse.symm
      _ ≤ q * (q + 1) * r ^ q + q * q ^ q := hLB
      _ ≤ (q + 1) * q ^ (q + 1) := hsmall
      _ = q * (q + 1) * q ^ q := hRHS
  have hqq : 1 ≤ q ^ q := Nat.pos_pow_of_pos q hq1
  have hcoef : q * (q + 1) < q * (q + 2) := by
    rw [← q_collapse q]; exact Nat.lt_add_of_pos_right hq1
  have hlt : q * (q + 1) * q ^ q < q * (q + 2) * q ^ q :=
    Nat.mul_lt_mul_of_pos_right hcoef hqq
  exact absurd hlt (Nat.not_lt.mpr hchain)

/-- ★★★ **The exact geometric completability boundary (an iff).**  Over the geometric
    denominator `d_i = q^i` (`q ≥ 2`), `CrossDetSmall (r^·) (q^·)` holds **iff** the
    cross-determinant grows strictly slower than the denominator, `r < q`.  Free below
    the rate threshold (`geom_crossdet_small`), broken at or above it
    (`geom_crossdet_overtake_sharp`).  Matching the denominator's exponential rate is
    not enough — the boundary is exactly `r < q`. -/
theorem geom_boundary_iff {q r : Nat} (hq : 2 ≤ q) :
    CrossDetSmall (fun i => r ^ i) (fun i => q ^ i) ↔ r < q :=
  ⟨fun hcs =>
      match Nat.lt_or_ge r q with
      | Or.inl hlt => hlt
      | Or.inr hge => absurd hcs (geom_crossdet_overtake_sharp hq hge),
   fun hlt => geom_crossdet_small (Nat.succ_le_of_lt hlt)⟩

end E213.Lib.Math.NumberSystems.Real213.GeometricThreshold
