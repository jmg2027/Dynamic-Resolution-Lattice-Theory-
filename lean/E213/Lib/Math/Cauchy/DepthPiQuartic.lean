import E213.Meta.Nat.PolyNat
import E213.Lib.Math.Cauchy.DepthPRecursiveInstances

/-!
# DepthPiQuartic — π's degree-4 cross-determinant ratio has divergence-depth 4

`DepthPRecursiveInstances` proved the general law (`newton_polyDepth`: every degree-`d`
discrete polynomial has depth `d`) and pinned e (depth 1) and π's degree-2 step
coefficient (depth 2).  The one piece it left as "residual nonlinear-`Nat`
bookkeeping" was π's **full degree-4 cross-determinant ratio** — the product of the
two Wallis step determinants `4(n+1)²` and `(2n+1)(2n+3)`:

    piRatio n = 4(n+1)² · (2n+1)(2n+3)        (= numStepDet · denStepDet)

This file closes it.  The obstruction was the absence of an ∅-axiom `ring`; the
reflection prover `Meta.Nat.PolyNat.poly_id` removes it.  Each forward difference is
established as an exact (truncation-free) identity `f(n+1) = f(n) + g(n)` — the
nonlinear expansion discharged by `poly_id` (mirror both sides as polynomial trees;
their Horner normal forms coincide by `rfl`).  Four differences take the quartic down
to the constant `384` (`= 4! · 16`, the leading coefficient times `4!`):

    piRatio → d1 (cubic) → d2 (quadratic) → d3 (linear) → 384

so `liftK 4 piRatio` is constant and `piRatio_polyDepth : polyDepth 4 piRatio`.
This confirms π's divergence depth 6 (1 cross-det + 1 ratio + 4 differences), now
fully ∅-axiom — the depth-arc B classical bridge closed for π as well as e.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthPiQuartic

open E213.Meta.Nat.PolyNat (poly_id)
open E213.Lib.Math.Cauchy.DivergenceLadder (diff liftK)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth liftK_diff_comm)
open E213.Lib.Math.Cauchy.DepthPRecursiveInstances (liftK_congr wallisDenCoeff)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-- π's cross-determinant ratio: the product of the two Wallis step determinants
    `4(n+1)²` (numerator) and `(2n+1)(2n+3)` (denominator).  Degree 4. -/
def piRatio (n : Nat) : Nat := 4 * (n+1) * (n+1) * ((2*n+1) * (2*n+3))

/-- `piRatio` is the numerator step determinant times the denominator step
    coefficient `(2n+1)(2n+3)` of `DepthPRecursiveInstances`. -/
theorem piRatio_eq (n : Nat) : piRatio n = 4 * (n+1) * (n+1) * wallisDenCoeff n := rfl

/-- The successive forward differences of `piRatio` (cubic, quadratic, linear). -/
private def d1 (n : Nat) : Nat := 64*n*n*n + 288*n*n + 440*n + 228
private def d2 (n : Nat) : Nat := 192*n*n + 768*n + 792
private def d3 (n : Nat) : Nat := 384*n + 960

/-! ## §1 — the exact difference identities (discharged by the reflection prover) -/

private theorem R1 (n : Nat) : piRatio (n+1) = piRatio n + d1 n :=
  poly_id
    (.mul (.mul (.mul (.C 4) (.add (.add .X (.C 1)) (.C 1))) (.add (.add .X (.C 1)) (.C 1)))
          (.mul (.add (.mul (.C 2) (.add .X (.C 1))) (.C 1)) (.add (.mul (.C 2) (.add .X (.C 1))) (.C 3))))
    (.add (.mul (.mul (.mul (.C 4) (.add .X (.C 1))) (.add .X (.C 1)))
               (.mul (.add (.mul (.C 2) .X) (.C 1)) (.add (.mul (.C 2) .X) (.C 3))))
          (.add (.add (.add (.mul (.mul (.mul (.C 64) .X) .X) .X) (.mul (.mul (.C 288) .X) .X))
                    (.mul (.C 440) .X)) (.C 228)))
    rfl n

private theorem R2 (n : Nat) : d1 (n+1) = d1 n + d2 n :=
  poly_id
    (.add (.add (.add (.mul (.mul (.mul (.C 64) (.add .X (.C 1))) (.add .X (.C 1))) (.add .X (.C 1)))
                    (.mul (.mul (.C 288) (.add .X (.C 1))) (.add .X (.C 1))))
               (.mul (.C 440) (.add .X (.C 1)))) (.C 228))
    (.add (.add (.add (.add (.mul (.mul (.mul (.C 64) .X) .X) .X) (.mul (.mul (.C 288) .X) .X))
                    (.mul (.C 440) .X)) (.C 228))
          (.add (.add (.mul (.mul (.C 192) .X) .X) (.mul (.C 768) .X)) (.C 792)))
    rfl n

private theorem R3 (n : Nat) : d2 (n+1) = d2 n + d3 n :=
  poly_id
    (.add (.add (.mul (.mul (.C 192) (.add .X (.C 1))) (.add .X (.C 1))) (.mul (.C 768) (.add .X (.C 1)))) (.C 792))
    (.add (.add (.add (.mul (.mul (.C 192) .X) .X) (.mul (.C 768) .X)) (.C 792))
          (.add (.mul (.C 384) .X) (.C 960)))
    rfl n

private theorem R4 (n : Nat) : d3 (n+1) = d3 n + 384 :=
  poly_id
    (.add (.mul (.C 384) (.add .X (.C 1))) (.C 960))
    (.add (.add (.mul (.C 384) .X) (.C 960)) (.C 384))
    rfl n

/-! ## §2 — the difference chain to the constant floor -/

private theorem diff_piRatio (n : Nat) : diff piRatio n = d1 n := by
  show piRatio (n+1) - piRatio n = d1 n
  rw [R1 n, Nat.add_comm (piRatio n) (d1 n)]; exact add_sub_cancel_right (d1 n) (piRatio n)

private theorem diff_d1 (n : Nat) : diff d1 n = d2 n := by
  show d1 (n+1) - d1 n = d2 n
  rw [R2 n, Nat.add_comm (d1 n) (d2 n)]; exact add_sub_cancel_right (d2 n) (d1 n)

private theorem diff_d2 (n : Nat) : diff d2 n = d3 n := by
  show d2 (n+1) - d2 n = d3 n
  rw [R3 n, Nat.add_comm (d2 n) (d3 n)]; exact add_sub_cancel_right (d3 n) (d2 n)

private theorem diff_d3 (n : Nat) : diff d3 n = 384 := by
  show d3 (n+1) - d3 n = 384
  rw [R4 n, Nat.add_comm (d3 n) 384]; exact add_sub_cancel_right 384 (d3 n)

/-- The 4-th finite difference of `piRatio` is the constant `384` — four differences
    take the quartic to a constant. -/
theorem liftK4_piRatio (n : Nat) : liftK 4 piRatio n = 384 := by
  rw [liftK_diff_comm 3 piRatio, liftK_congr 3 (diff piRatio) d1 diff_piRatio n,
      liftK_diff_comm 2 d1, liftK_congr 2 (diff d1) d2 diff_d1 n,
      liftK_diff_comm 1 d2, liftK_congr 1 (diff d2) d3 diff_d2 n]
  show diff d3 n = 384
  exact diff_d3 n

/-! ## §3 — π's cross-determinant ratio is depth 4 -/

/-- ★★★ **π's cross-determinant ratio has divergence-depth 4.**  `polyDepth 4
    piRatio` — the degree-4 product `4(n+1)²(2n+1)(2n+3)` of the two Wallis step
    determinants reaches its constant floor (`384`) after exactly four finite
    differences.  Confirms π's divergence depth 6 (1 cross-det + 1 ratio + 4
    differences) ∅-axiom — the depth-arc B bridge closed for π, with the nonlinear
    expansion discharged by the reflection prover `Meta.Nat.PolyNat`. -/
theorem piRatio_polyDepth : polyDepth 4 piRatio :=
  fun n => by rw [liftK4_piRatio n, liftK4_piRatio 0]

end E213.Lib.Math.Cauchy.DepthPiQuartic
