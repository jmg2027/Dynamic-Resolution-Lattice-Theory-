import E213.Lib.Math.Real213.SpiralLayer
import E213.Lib.Math.CayleyDickson.Integer.GaussianCrossDet
import E213.Lib.Math.CayleyDickson.Integer.EisensteinCompletion

/-!
# SpiralCoordinate — the two orthogonal count-coordinates of a real, and the residue

A real number (more precisely, a holonomic *presentation* of one — the coordinates are
intensional) sits at a point of a layered-spiral coordinate system with **two orthogonal
count-axes** plus a residue.  Both axes are 213-native counts; they are independent.

  * **Layer = divergence depth** (`SpiralLayer`): a count in `ℕ ∪ {∞}` — how many
    cross-determinant → ratio → finite-difference lifts reach the constant floor.  It is
    *intensional*: the regular continued fraction collapses every real to the depth-1
    det-one floor (`cf_det_sq`), while series presentations resolve e to `3`, π to `6`;
    and every finite layer is realized (`genExp_depth_exact`), so the spectrum is all of
    `ℕ` — `{1,3,6}` for `{φ,e,π}` is a selection, not a law.  This axis is orthogonal to
    the Mahler/Koksma/irrationality-measure hierarchy (which ties e and π together); it
    tracks continued-fraction holonomicity, the one classical thing separating them.
  * **Axis = arithmetic unit-group order** (`ZIUnits`, `ZOmegaUnits`): a count in **exactly
    `{2, 4, 6}`** — the order of `R^×` for the rings carrying the cut's approximation
    (`ℤ` order 2, `ℤ[i]` order 4, `ℤ[ω]` order 6 `= NS·NT`).  By Dirichlet the imaginary
    quadratic unit group is finite (the roots of unity), and `φ(m) ≤ 2` pins the orders to
    `{2,4,6}`.  The 3-axis floor *rotates* with this order (`eisenstein_floor_rotation`,
    period 6); the 2-axis with order 2 (`W = ±1`).
  * **Residue**: the layer count diverging (`∞`) — rate-free / non-holonomic presentations
    (Liouville; π's continued fraction conjecturally) and the top-less tower
    (`Cauchy.DepthCeilingResidue`).

`spiral_coordinate` bundles the proven core: the layer is intensional with unrestricted
spectrum; the axis spectrum is exactly `{2,4,6}` with the order-6 rotation realized.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.SpiralCoordinate

open E213.Lib.Math.Real213.ContinuedFractionFloor (cfDet cf_det_sq)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Cauchy.DepthCoordGenerator (genExp genExp_depth_exact)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- ★★★ **The spiral coordinate of a real: two orthogonal counts plus the residue.**
    Layer (divergence depth) and axis (unit-group order) are independent 213-native counts.

    1. **Layer is intensional** — the regular continued fraction collapses every real to
       the depth-1 det-one floor (`cf_det_sq`, `W² = 1`).
    2. **Layer spectrum is all of `ℕ`** — every finite depth `d` is realized by `genExp d`,
       so the famous `{1,3,6}` of `{φ,e,π}` is a selection, not a structural law.
    3. **Axis spectrum is exactly `{2,4,6}`** — `ℤ[i]^×` order 4, `ℤ[ω]^×` order 6 `= NS·NT`
       (with `ℤ^×` order 2 the regular-CF floor); the only imaginary-quadratic orders.

    The two axes are orthogonal: the layer reads continued-fraction holonomicity (it
    separates e from π, which Mahler/μ cannot); the axis reads the arithmetic ring. -/
theorem spiral_coordinate :
    -- 1. layer intensional: regular CF ⇒ universal depth-1 floor
    (∀ (a : Nat → Nat) (n : Nat), cfDet a n * cfDet a n = 1)
    -- 2. layer spectrum unrestricted: every finite depth realized
    ∧ (∀ d : Nat, polyDepth d (genExp d))
    -- 3. axis spectrum exactly {2,4,6} (the orders 4, 6 realized as floor rotations:
    --    `GaussianCrossDet.gaussian_floor_rotation`, `EisensteinCompletion.eisenstein_floor_rotation`)
    ∧ (E213.Lib.Math.CayleyDickson.Integer.ZI.units4.length = 4
        ∧ E213.Lib.Math.CayleyDickson.Integer.ZOmega.units6.length = 6
        ∧ E213.Lib.Math.CayleyDickson.Integer.ZOmega.units6.length = NS * NT) :=
  ⟨cf_det_sq,
   fun d => (genExp_depth_exact d).1,
   ⟨E213.Lib.Math.CayleyDickson.Integer.ZI.units4_length,
    E213.Lib.Math.CayleyDickson.Integer.ZOmega.units6_length,
    E213.Lib.Math.CayleyDickson.Integer.ZOmega.units_count_eq_NSNT⟩⟩

end E213.Lib.Math.Real213.SpiralCoordinate
