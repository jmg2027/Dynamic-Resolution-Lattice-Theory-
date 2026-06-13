import E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetOvertake
import E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm
import E213.Lib.Math.Analysis.Cauchy.Euler
import E213.Meta.Nat.PolyNat
import E213.Meta.Tactic.NatHelper

/-!
# PresentationDependence — `CrossDetSmall` is a property of the representation, not the real

The completability bridge `CrossDetSmall ⟹ free modulus` is a *sufficient* condition on
a num/den presentation `a_i/d_i`.  This file makes precise that it reads the
**representation**, not the real: the underlying real (the decidable cut) is invariant
under a common rescaling `(a, d) ↦ (c·a, c·d)`, while `CrossDetSmall` is not — the
cross-determinant scales by `c²` against a denominator scaling by `c`, so the smallness
condition is strictly harder for `c ≥ 2` and can fail though the real is unchanged.

  * ★ `rcut_rescale` — the real is rescaling-invariant: `rcut (c·a) (c·d) = rcut a d`
    (the cut cancels the common factor, `c ≥ 1`).
  * ★ `crossdet_rescale` — the rescaled cross-determinant is `c²·W`:
    `(c·a)_{i+1}(c·d)_i = (c·a)_i(c·d)_{i+1} + c²·W_i`.
  * ★★★ `crossDetSmall_is_presentation_dependent` — the concrete witness, on e: its
    standard convergents `eulerNum/eulerDen` satisfy `CrossDetSmall` (e is rate-carrying,
    `W = d`), but the `×2` representation `2·eulerNum / 2·eulerDen` — *the same real*
    (`rcut` equal) — has cross-determinant `4·eulerDen` against denominator `2·eulerDen`
    and **fails** `CrossDetSmall` already at `i = 1` (`10 ≤ 8`).  So whether the bridge
    applies is a fact about the presentation, not the number.

This is the "deficiency of the presentation, not of the real" thesis
(`holonomic_modulus.md`) made into a theorem: completability via the cross-determinant
bridge is presentation-relative, and the cut is the rescaling-invariant content.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.PresentationDependence

open E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetOvertake (CrossDetSmall)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (rcut)
open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen)
open E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm (euler_cross_det)
open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper (add_mul mul_assoc mul_mul_mul_comm_213)

/-! ## §1 — the real is rescaling-invariant -/

private theorem decide_mul_le (c X Y : Nat) (hc : 1 ≤ c) :
    decide (c * X ≤ c * Y) = decide (X ≤ Y) := by
  cases h : decide (X ≤ Y) with
  | true  => exact decide_eq_true (Nat.mul_le_mul_left c (of_decide_eq_true h))
  | false => exact decide_eq_false (fun hcon => (of_decide_eq_false h)
                (Nat.le_of_mul_le_mul_left hcon hc))

/-- ★ **The cut is rescaling-invariant.**  `rcut (c·a) (c·d) = rcut a d` for `c ≥ 1`:
    the decidable cut `a_i·k ≤ d_i·m` cancels the common factor `c`, so the real a
    presentation defines does not change under `(a, d) ↦ (c·a, c·d)`. -/
theorem rcut_rescale (c : Nat) (hc : 1 ≤ c) (a d : Nat → Nat) (i m k : Nat) :
    rcut (fun i => c * a i) (fun i => c * d i) i m k = rcut a d i m k := by
  show decide ((c * a i) * k ≤ (c * d i) * m) = decide (a i * k ≤ d i * m)
  rw [mul_assoc c (a i) k, mul_assoc c (d i) m]
  exact decide_mul_le c (a i * k) (d i * m) hc

/-! ## §2 — the cross-determinant scales by `c²` -/

/-- ★ **The rescaled cross-determinant is `c²·W`.**  Rescaling `(a, d)` by `c`
    multiplies the cross-determinant by `c²` while the denominator scales by `c` — the
    source of the asymmetry that makes `CrossDetSmall` representation-dependent. -/
theorem crossdet_rescale (c : Nat) {a d W : Nat → Nat}
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i) (i : Nat) :
    (c * a (i+1)) * (c * d i) = (c * a i) * (c * d (i+1)) + (c * c) * W i := by
  have lhs : (c * a (i+1)) * (c * d i) = (c * c) * (a (i+1) * d i) := by
    rw [mul_mul_mul_comm_213]
  rw [lhs, hW i, Nat.mul_add]
  congr 1
  rw [mul_mul_mul_comm_213]

/-! ## §3 — the concrete witness on e -/

/-- e's standard convergents satisfy `CrossDetSmall` (`W = d = eulerDen`): the rung
    that makes e rate-carrying, `i(i+1)+i = i(i+2) ≤ (i+1)²`. -/
theorem e_unscaled_small : CrossDetSmall eulerDen eulerDen := by
  intro i _
  show i * (i+1) * eulerDen i + i * eulerDen i ≤ (i+1) * eulerDen (i+1)
  rw [show eulerDen (i+1) = (i+1) * eulerDen i from rfl, ← add_mul, ← mul_assoc]
  refine Nat.mul_le_mul_right (eulerDen i) ?_
  have h : (i+1) * (i+1) = i * (i+1) + i + 1 :=
    poly_id (.mul (.add .X (.C 1)) (.add .X (.C 1)))
            (.add (.add (.mul .X (.add .X (.C 1))) .X) (.C 1)) rfl i
  rw [h]; exact Nat.le_succ _

/-- The `×2` representation of e carries cross-determinant `2²·eulerDen` (= `4·eulerDen`)
    against denominator `2·eulerDen` — a direct instance of `crossdet_rescale`. -/
theorem e_scaled_crossdet (i : Nat) :
    (2 * eulerNum (i+1)) * (2 * eulerDen i)
      = (2 * eulerNum i) * (2 * eulerDen (i+1)) + (2 * 2) * eulerDen i :=
  crossdet_rescale 2 euler_cross_det i

/-- The `×2` representation **fails** `CrossDetSmall`, already at `i = 1`:
    `1·2·(4·eulerDen 1) + 1·(2·eulerDen 1) = 10` exceeds `2·(2·eulerDen 2) = 8`
    (`eulerDen 1 = 1`, `eulerDen 2 = 2`). -/
theorem e_scaled_breaks :
    ¬ CrossDetSmall (fun i => 4 * eulerDen i) (fun i => 2 * eulerDen i) := by
  intro hcs
  exact absurd (hcs 1 (by decide)) (by decide)

/-- ★★★ **`CrossDetSmall` is presentation-dependent.**  For the *same real* (the cut is
    rescaling-invariant, third conjunct), e's standard representation satisfies the
    completability condition (first conjunct) while its `×2` representation does not
    (second conjunct).  So the cross-determinant bridge reads the presentation, not the
    number — the cut is the invariant content, the smallness condition is not. -/
theorem crossDetSmall_is_presentation_dependent :
    CrossDetSmall eulerDen eulerDen
    ∧ ¬ CrossDetSmall (fun i => 4 * eulerDen i) (fun i => 2 * eulerDen i)
    ∧ (∀ i m k, rcut (fun i => 2 * eulerNum i) (fun i => 2 * eulerDen i) i m k
                = rcut eulerNum eulerDen i m k) :=
  ⟨e_unscaled_small, e_scaled_breaks,
   fun i m k => rcut_rescale 2 (by decide) eulerNum eulerDen i m k⟩

end E213.Lib.Math.NumberSystems.Real213.PresentationDependence
