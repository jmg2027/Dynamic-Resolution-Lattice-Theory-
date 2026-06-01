import E213.Lib.Math.Real213.CrossDetOvertake
import E213.Lib.Math.Real213.LiouvilleModulus
import E213.Lib.Math.Cauchy.DepthClosure
import E213.Lib.Math.Cauchy.DepthCoordGenerator
import E213.Lib.Math.Cauchy.DepthCeilingResidue

/-!
# TowerNativeCompleteness — the program, closed

"Which reals complete?" is, in the resolution tower, a comparison of two growth-axes
(cross-determinant `W` vs denominator `d`) — no irrationality measure, no LEM.  The
five pieces of that program are each a ∅-axiom theorem; this file bundles them.

  * **Boundary** (`CrossDetOvertake.completability_boundary`) — over the fixed
    denominator `2^i`, a constant cross-determinant completes (free) and the double
    exponential `2^{2^i}` overtakes and breaks the smallness condition.
  * **Liouville** (`LiouvilleModulus.liouville_W_eq_denom_coordinate`) — its
    cross-determinant equals its denominator (`W_k = c^{k!}`), so on the
    cross-determinant axis a Liouville number is as tame as e and carries a free
    modulus; the value-axis depth-∞ is irrelevant.
  * **Closure** (`DepthClosure.rate_carrying_tower_closure`) — the finite-coordinate
    class is closed under `×` and the exponent axis, breaking exactly at the
    exponential boundary.
  * **Generator** (`DepthCoordGenerator.tower_is_coordinate_system`) — every tower
    coordinate is realized by an explicit sequence; the `ω^ω` ladder is generated
    top-down.
  * **Residue** (`DepthCeilingResidue.ceiling_residue_is_pointing_residue`) — the
    tower has no top: naming the ceiling-raising is the Cantor self-cover, so the
    boundary of constructive completeness is the residue of pointing.

★★★ `tower_native_completeness_program` is the single ∅-axiom statement that the five
hold together.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.TowerNativeCompleteness

open E213.Lib.Math.Real213.CrossDetOvertake
  (CrossDetSmall denomExp crossW completability_boundary)
open E213.Lib.Math.Real213.LiouvilleModulus
  (liouNum liouDen liouville_W_eq_denom_coordinate)
open E213.Lib.Math.Cauchy.DepthLiouvilleCoord (fact)
open E213.Lib.Math.Cauchy.DepthTower (ratioLift)
open E213.Lib.Math.Cauchy.DepthExponentRecursion (totMono expSeq)
open E213.Lib.Math.Cauchy.DepthDoubleExp (twoPow)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Cauchy.DepthClosure
  (FinDiffDepth FinRatioDepth rate_carrying_tower_closure)
open E213.Lib.Math.Cauchy.DepthCoordGenerator (genExp tower_is_coordinate_system)
open E213.Lib.Math.Cauchy.DepthOmegaTower (expTower Coord coordLt)
open E213.Lib.Math.Cauchy.DepthCeilingResidue (ceiling_residue_is_pointing_residue)
open E213.Lens.FlatOntology (Object1)
open E213.Theory (Raw)

/-- ★★★ **The tower-native real-number program, closed.**  The completability boundary,
    the Liouville adjudication (cross-determinant = denominator), the closure of the
    finite-coordinate class under `×`/exponent, the coordinate generator, and the
    residue tie — all ∅-axiom, all internal to the resolution tower.  Completability is
    a stratified, self-generating, foundation-touching structure, not a yes/no fact
    about individual reals. -/
theorem tower_native_completeness_program :
    -- boundary (T1)
    (CrossDetSmall (fun _ => 1) denomExp ∧ ¬ CrossDetSmall crossW denomExp)
    -- Liouville: cross-determinant = denominator, factorial-tier coordinate (T2)
    ∧ (∀ c, (∀ k, liouNum c (k+1) * liouDen c k
                  = liouNum c k * liouDen c (k+1) + liouDen c k)
            ∧ (∀ k, liouDen c k = c ^ fact k)
            ∧ (∀ n, ratioLift fact n = n + 1))
    -- closure of the finite-coordinate class, breaking at the boundary (T3)
    ∧ ((∀ c, 1 ≤ c → ∀ e₁ e₂, totMono e₁ → totMono e₂ →
              FinDiffDepth e₁ → FinDiffDepth e₂ →
              FinRatioDepth (expSeq c (fun m => e₁ m + e₂ m)))
        ∧ (∀ c, 1 ≤ c → ∀ e, totMono e → FinDiffDepth e → FinRatioDepth (expSeq c e))
        ∧ ¬ FinDiffDepth twoPow
        ∧ ¬ FinRatioDepth (expSeq 2 twoPow))
    -- the tower is a coordinate system, generated top-down (T4)
    ∧ ((∀ d, polyDepth d (genExp d))
        ∧ (∀ c r, expTower c (r+1) = expSeq c (expTower c r))
        ∧ (∀ r a (p q : Coord r), coordLt (r+1) (a, p) (a+1, q)))
    -- the tower has no top = the residue of pointing (the deep tie)
    ∧ ((Function.Injective Object1 ∧ ¬ Function.Surjective Object1)
        ∧ (¬ ∃ g : Raw → (Raw → Bool), Function.Surjective g)) :=
  ⟨completability_boundary,
   fun c => liouville_W_eq_denom_coordinate c,
   rate_carrying_tower_closure,
   tower_is_coordinate_system,
   ceiling_residue_is_pointing_residue⟩

end E213.Lib.Math.Real213.TowerNativeCompleteness
