import E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
import E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm
import E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus
import E213.Lib.Math.NumberSystems.Real213.LiouvilleModulus
import E213.Meta.Nat.PolyNat

/-!
# CrossDetEqDenom — self-similar cross-determinant (`W = d`) ⟹ free modulus

Two structurally different reals share one feature on the cross-determinant axis:
their convergents' cross-determinant **equals the denominator**, `W_i = d_i`.

  * e (`EulerDivergenceForm.euler_cross_det`): `eulerNum_{n+1}·eulerDen_n =
    eulerNum_n·eulerDen_{n+1} + eulerDen_n`;
  * the Liouville constant (`LiouvilleModulus.liou_cross_det`): the same shape.

This is the middle rung between the algebraic floor (`W` constant, det-one,
`DepthFloorDetOne`) and the overtake (`W ≫ d`, `CrossDetOvertake`).  This file extracts
the one theorem behind both: a convergent num/den with `W = d` and a denominator
growing at least as `i(i+2)·d_i ≤ (i+1)·d_{i+1}` carries a free total ∅-axiom modulus
`N(m,k) = k+2`.  It is a direct specialization of
`CrossDetOvertake.crossdet_small_total_modulus` at `W := d`, with `CrossDetSmall d d`
collapsing (`i(i+1)+i = i(i+2)`) to the growth condition.

  * ★★★ `crossdet_eq_denom_total_modulus` — the general theorem.
  * `euler_total_modulus_via_eq_denom`, `liouville_total_modulus_via_eq_denom` — e and
    the Liouville constant reproven as one-line instances, the growth condition reducing
    to `i(i+2)+1 = (i+1)²` (e) and `i(i+2) ≤ (i+1)·g_i` (Liouville).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.CrossDetEqDenom

open E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake (CrossDetSmall crossdet_small_total_modulus)
open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper (add_mul mul_assoc)

/-- ★★★ **Self-similar cross-determinant ⟹ free modulus.**  A convergent num/den
    `a/d` whose cross-determinant equals its denominator (`W_i = d_i`, `hWeqD`), with
    positive denominators and the growth condition `i(i+2)·d_i ≤ (i+1)·d_{i+1}`
    (`hgrow` — exactly `CrossDetSmall d d` after `i(i+1)+i = i(i+2)`), carries a free
    total ∅-axiom modulus `N(m,k) = k+2`.  The shared mechanism behind e and the
    Liouville constant. -/
theorem crossdet_eq_denom_total_modulus {a d : Nat → Nat}
    (hd : ∀ i, 1 ≤ d i)
    (hWeqD : ∀ i, a (i + 1) * d i = a i * d (i + 1) + d i)
    (hgrow : ∀ i, 1 ≤ i → i * (i + 2) * d i ≤ (i + 1) * d (i + 1))
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i + 1) < a (i + 1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  crossdet_small_total_modulus d hd hWeqD
    (fun i hi => by
      have hcollapse : i * (i + 1) * d i + i * d i = i * (i + 2) * d i := by
        rw [← add_mul]
        have hp : i * (i + 1) + i = i * (i + 2) :=
          poly_id (.add (.mul .X (.add .X (.C 1))) .X)
                  (.mul .X (.add .X (.C 2))) rfl i
        rw [hp]
      show i * (i + 1) * d i + i * d i ≤ (i + 1) * d (i + 1)
      rw [hcollapse]; exact hgrow i hi)
    hmono hmonoS m k hk

/-! ## e is a one-line instance -/

open E213.Lib.Math.Analysis.Cauchy.EulerSeq (eulerNum eulerDen eulerDen_pos)
open E213.Lib.Math.Analysis.Cauchy.EulerDivergenceForm (euler_cross_det)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.EulerModulus (euler_hmono euler_hmonoS)

/-- e's total modulus, through `crossdet_eq_denom_total_modulus`: the growth condition
    `i(i+2)·eulerDen_i ≤ (i+1)·eulerDen_{i+1}` is `i(i+2)+1 = (i+1)²` after
    `eulerDen_{i+1} = (i+1)·eulerDen_i`. -/
theorem euler_total_modulus_via_eq_denom (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut eulerNum eulerDen i m k = rcut eulerNum eulerDen j m k :=
  crossdet_eq_denom_total_modulus
    eulerDen_pos
    euler_cross_det
    (fun i _ => by
      show i * (i + 2) * eulerDen i ≤ (i + 1) * eulerDen (i + 1)
      rw [show eulerDen (i+1) = (i+1)*eulerDen i from rfl, ← mul_assoc]
      refine Nat.mul_le_mul_right (eulerDen i) ?_
      have h : i * (i + 2) + 1 = (i + 1) * (i + 1) :=
        poly_id (.add (.mul .X (.add .X (.C 2))) (.C 1))
                (.mul (.add .X (.C 1)) (.add .X (.C 1))) rfl i
      exact Nat.le_of_lt (h ▸ Nat.lt_succ_self _))
    euler_hmono euler_hmonoS m k hk

/-! ## the Liouville constant is a one-line instance -/

open E213.Lib.Math.NumberSystems.Real213.LiouvilleModulus
  (liouNum liouDen g liou_hd liou_cross_det liou_hmono liou_hmonoS succ_le_g)

/-- The Liouville constant's total modulus, through `crossdet_eq_denom_total_modulus`:
    the growth condition reduces to `i(i+2) ≤ (i+1)·g_i` via `succ_le_g`. -/
theorem liouville_total_modulus_via_eq_denom (c : Nat) (hc : 2 ≤ c) (m k : Nat)
    (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (liouNum c) (liouDen c) i m k = rcut (liouNum c) (liouDen c) j m k :=
  have hc1 : 1 ≤ c := Nat.le_trans (by decide) hc
  crossdet_eq_denom_total_modulus
    (liou_hd c hc1)
    (liou_cross_det c)
    (fun i _ => by
      show i * (i + 2) * liouDen c i ≤ (i + 1) * (g c i * liouDen c i)
      have hbound : i * (i + 2) ≤ (i + 1) * g c i := by
        calc i * (i + 2)
            ≤ (i + 1) * (i + 1) := by
              have hp : i * (i + 2) + 1 = (i + 1) * (i + 1) :=
                poly_id (.add (.mul .X (.add .X (.C 2))) (.C 1))
                        (.mul (.add .X (.C 1)) (.add .X (.C 1))) rfl i
              exact Nat.le_of_lt (hp ▸ Nat.lt_succ_self _)
          _ ≤ (i + 1) * g c i := Nat.mul_le_mul_left (i + 1) (succ_le_g c i hc)
      calc i * (i + 2) * liouDen c i
          ≤ ((i + 1) * g c i) * liouDen c i := Nat.mul_le_mul_right _ hbound
        _ = (i + 1) * (g c i * liouDen c i) := by rw [mul_assoc])
    (liou_hmono c hc1) (liou_hmonoS c hc1) m k hk

end E213.Lib.Math.NumberSystems.Real213.CrossDetEqDenom
