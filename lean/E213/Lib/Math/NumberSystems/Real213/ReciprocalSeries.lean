import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetEqDenom
import E213.Lib.Math.Analysis.Cauchy.DepthLiouvilleCoord
import E213.Meta.Nat.PolyNat
import E213.Meta.Tactic.NatHelper

/-!
# ReciprocalSeries — the `W = d` line is a one-parameter reference family

The `W = d` relation `a_{i+1}d_i = a_i d_{i+1} + d_i` cross-divides to
`a_{i+1}/d_{i+1} − a_i/d_i = 1/d_{i+1}`: a `W = d` real is exactly a **reciprocal-
denominator series** `Σ 1/d_j`, whose convergents step by a *unit* numerator over the
next denominator.  Such a real is built from a single parameter — the ratio sequence
`g_i = d_{i+1}/d_i` (a divisibility chain keeping the convergents integral):

> `den g 0 = 1`,  `den g (i+1) = g_i · den g i`;
> `num g 0 = 1`,  `num g (i+1) = g_i · num g i + 1`.

By construction `num g (i+1) · den g i = num g i · den g (i+1) + den g i` (`W = d`,
`recip_cross_det`), so this is the **canonical inhabitant of the `y = x` line for the
chosen `g`**, and it carries a free modulus exactly when the ratio grows at least
linearly:

  * ★★★ `recip_total_modulus` — for any ratio `g` with `i+1 ≤ g_i` (`i ≥ 1`), the
    reciprocal series `Σ 1/den g` completes with a free total ∅-axiom modulus.
  * `den_linear_is_factorial` — the linear-ratio point `g_i = i+1` is **e**
    (`den (·+1) = factorial`, `Σ 1/j!`); the fast-ratio points (`g_i = c^{i·i!}`) are
    the Liouville constants.  The diagonal is thus a growth-graded family, e and
    Liouville two of its points.

So the `W = d` line is a parametrized **reference family**: one ratio sequence `g`
names one self-completing real, graded by `g`'s growth, with the completion threshold
`g_i ≳ i` read directly off the parameter.  (Whether *every* real admits such a
representation — a universal reciprocal-series / Engel–Sylvester chart — is a deeper
question, not settled here.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ReciprocalSeries

open E213.Lib.Math.NumberSystems.Real213.CrossDetEqDenom (crossdet_eq_denom_total_modulus)
open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Lib.Math.Analysis.Cauchy.DepthLiouvilleCoord (fact fact_succ)
open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper
  (mul_assoc add_mul add_sub_cancel_right mul_mul_mul_comm_213 le_of_mul_le_mul_right)

/-! ## §1 — the family, indexed by the ratio `g` -/

/-- Denominators from the ratio sequence: `den g 0 = 1`, `den g (i+1) = g_i · den g i`. -/
def den (g : Nat → Nat) : Nat → Nat
  | 0   => 1
  | i+1 => g i * den g i

/-- Numerators of `Σ 1/den g`: `num g 0 = 1`, `num g (i+1) = g_i · num g i + 1`. -/
def num (g : Nat → Nat) : Nat → Nat
  | 0   => 1
  | i+1 => g i * num g i + 1

theorem den_pos (g : Nat → Nat) (hg : ∀ i, 1 ≤ g i) : ∀ i, 1 ≤ den g i
  | 0   => Nat.le_refl 1
  | i+1 => Nat.mul_pos (hg i) (den_pos g hg i)

theorem num_pos (g : Nat → Nat) : ∀ i, 1 ≤ num g i
  | 0   => Nat.le_refl 1
  | i+1 => by show 1 ≤ g i * num g i + 1; exact Nat.le_add_left 1 _

/-! ## §2 — `W = d` by construction; the unit-increment reading -/

/-- ★ **`W = d` for the whole family.**  `num g (i+1) · den g i = num g i · den g (i+1)
    + den g i` — the cross-determinant is the denominator, by construction, for every
    ratio `g`. -/
theorem recip_cross_det (g : Nat → Nat) (i : Nat) :
    num g (i+1) * den g i = num g i * den g (i+1) + den g i := by
  show (g i * num g i + 1) * den g i = num g i * (g i * den g i) + den g i
  rw [add_mul, Nat.one_mul]
  congr 1
  rw [Nat.mul_comm (g i) (num g i), mul_assoc]

/-- ★ **The unit increment.**  `num g (i+1)·den g i − num g i·den g (i+1) = den g i` —
    the convergents step by exactly `1/den g (i+1)`, the defining feature of a
    reciprocal-denominator series. -/
theorem recip_unit_increment (g : Nat → Nat) (i : Nat) :
    num g (i+1) * den g i - num g i * den g (i+1) = den g i := by
  rw [recip_cross_det g i, Nat.add_comm, add_sub_cancel_right]

/-! ## §3 — the generator hypotheses (generic in `g`) -/

theorem recip_hmonoS (g : Nat → Nat) (hg : ∀ i, 1 ≤ g i) :
    ∀ i, num g i * den g (i+1) < num g (i+1) * den g i := by
  intro i
  show num g i * (g i * den g i) < (g i * num g i + 1) * den g i
  have hL : num g i * (g i * den g i) = g i * num g i * den g i := by
    rw [← mul_assoc, Nat.mul_comm (num g i) (g i)]
  have hR : (g i * num g i + 1) * den g i = g i * num g i * den g i + den g i := by
    rw [add_mul, Nat.one_mul]
  rw [hL, hR]; exact Nat.lt_add_of_pos_right (den_pos g hg i)

private theorem rearr (w x y z : Nat) : (w*x)*(y*z) = (w*z)*(y*x) := by
  rw [mul_mul_mul_comm_213 w x y z, mul_mul_mul_comm_213 w z y x, Nat.mul_comm x z]

private theorem ratio_trans (g : Nat → Nat) (hg : ∀ i, 1 ≤ g i) (N M i : Nat)
    (h1 : num g N * den g M ≤ num g M * den g N)
    (h2 : num g M * den g i ≤ num g i * den g M) :
    num g N * den g i ≤ num g i * den g N := by
  have hposM : 0 < num g M * den g M := Nat.mul_pos (num_pos g M) (den_pos g hg M)
  have key : (num g N * den g i) * (num g M * den g M)
      ≤ (num g i * den g N) * (num g M * den g M) := by
    calc (num g N * den g i) * (num g M * den g M)
        = (num g N * den g M) * (num g M * den g i) := rearr _ _ _ _
      _ ≤ (num g M * den g N) * (num g i * den g M) := Nat.mul_le_mul h1 h2
      _ = (num g i * den g N) * (num g M * den g M) := by
          rw [mul_mul_mul_comm_213 (num g M) (den g N) (num g i) (den g M),
              Nat.mul_comm (num g M) (num g i),
              mul_mul_mul_comm_213 (num g i) (num g M) (den g N) (den g M),
              rearr (num g i) (den g N) (num g M) (den g M)]
  exact le_of_mul_le_mul_right hposM key

theorem recip_hmono (g : Nat → Nat) (hg : ∀ i, 1 ≤ g i) :
    ∀ N i, N ≤ i → num g N * den g i ≤ num g i * den g N := by
  intro N i hNi
  obtain ⟨t, rfl⟩ := Nat.le.dest hNi
  induction t with
  | zero => exact Nat.le_of_eq (by rw [Nat.add_zero])
  | succ s ih =>
    rw [show N+(s+1) = (N+s)+1 from rfl]
    exact ratio_trans g hg N (N+s) ((N+s)+1) (ih (Nat.le_add_right N s))
      (Nat.le_of_lt (recip_hmonoS g hg (N+s)))

/-- The denominator-growth condition (in `crossdet_eq_denom`'s `i(i+2)` form): a ratio
    `g_i ≥ i+1` makes the reciprocal series complete. -/
theorem recip_growth (g : Nat → Nat) (hg2 : ∀ i, 1 ≤ i → i + 1 ≤ g i) :
    ∀ i, 1 ≤ i → i * (i + 2) * den g i ≤ (i + 1) * den g (i + 1) := by
  intro i hi
  show i * (i + 2) * den g i ≤ (i + 1) * (g i * den g i)
  have hbound : i * (i + 2) ≤ (i + 1) * g i := by
    calc i * (i + 2)
        ≤ (i + 1) * (i + 1) := by
          have h : i * (i + 2) + 1 = (i + 1) * (i + 1) :=
            poly_id (.add (.mul .X (.add .X (.C 2))) (.C 1))
                    (.mul (.add .X (.C 1)) (.add .X (.C 1))) rfl i
          exact Nat.le_of_lt (h ▸ Nat.lt_succ_self _)
      _ ≤ (i + 1) * g i := Nat.mul_le_mul_left (i + 1) (hg2 i hi)
  calc i * (i + 2) * den g i
      ≤ ((i + 1) * g i) * den g i := Nat.mul_le_mul_right _ hbound
    _ = (i + 1) * (g i * den g i) := by rw [mul_assoc]

/-! ## §4 — the free modulus, generic in `g` -/

/-- ★★★ **Every linearly-growing reciprocal series completes.**  For any ratio
    sequence `g` with `i + 1 ≤ g_i` (`i ≥ 1`), the reciprocal-denominator series
    `Σ 1/den g` — the canonical `W = d` real for that `g` — carries a free total
    ∅-axiom modulus `N(m,k) = k+2`, through `crossdet_eq_denom_total_modulus`.  The
    `W = d` line is thus a `g`-parametrized family of self-completing reals. -/
theorem recip_total_modulus (g : Nat → Nat) (hg : ∀ i, 1 ≤ g i)
    (hg2 : ∀ i, 1 ≤ i → i + 1 ≤ g i) (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (num g) (den g) i m k = rcut (num g) (den g) j m k :=
  crossdet_eq_denom_total_modulus (den_pos g hg) (recip_cross_det g)
    (recip_growth g hg2) (recip_hmono g hg) (recip_hmonoS g hg) m k hk

/-! ## §5 — the named points on the line -/

/-- The **linear-ratio point** `g_i = i+1` is e: its denominators are the factorials,
    so `Σ 1/den (·+1) = Σ 1/j!`.  e is the slowest-growing point on the line that still
    completes (`g_i = i+1` meets the threshold `i+1 ≤ g_i` with equality). -/
theorem den_linear_is_factorial : ∀ k, den (fun i => i + 1) k = fact k
  | 0   => rfl
  | k+1 => by
    show (k + 1) * den (fun i => i + 1) k = fact (k + 1)
    rw [den_linear_is_factorial k, fact_succ]

/-- e completes as the linear-ratio reciprocal series (`g_i = i+1`). -/
theorem euler_as_reciprocal_series (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (num (fun i => i + 1)) (den (fun i => i + 1)) i m k
        = rcut (num (fun i => i + 1)) (den (fun i => i + 1)) j m k :=
  recip_total_modulus (fun i => i + 1) (fun i => Nat.succ_pos i)
    (fun i _ => Nat.le_refl (i + 1)) m k hk

end E213.Lib.Math.NumberSystems.Real213.ReciprocalSeries
