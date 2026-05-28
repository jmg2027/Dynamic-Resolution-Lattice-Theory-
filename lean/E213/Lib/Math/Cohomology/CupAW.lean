import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Lib.Math.Cohomology.CupAW.Bilinear
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.CupAW.Leibniz
import E213.Lib.Math.Cohomology.CupAW.LeibnizBzBridge
import E213.Lib.Math.Cohomology.CupAW.Leibniz21Final
import E213.Lib.Math.Cohomology.CupAW.Leibniz22Final
import E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed
import E213.Lib.Math.Cohomology.CupAW.LeibnizScaling
import E213.Lib.Math.Cohomology.CupAW.LeibnizSmall
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift21Alpha
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22
import E213.Lib.Math.Cohomology.CupAW.LeibnizAlgLift22Alpha
import E213.Lib.Math.Cohomology.CupAW.LeibnizMid
import E213.Lib.Math.Cohomology.CupAW.Pointwise
import E213.Lib.Math.Cohomology.CupAW.PointwiseBilinear
import E213.Lib.Math.Cohomology.CupAW.Zero

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.CupAW`.

  Alexander–Whitney cup product (`cupAW`) on the 213-native
  cochain complex.  Companion to `Cup/` (strict cup product);
  `cupAW` is the homotopy-coherent variant that survives the
  algebraic-lift constructions.

  ## Core

    * `Core`           — `cupAW p q : Cochain n p → Cochain n q
                          → Cochain n (p+q)` definition
    * `Zero`           — `cupAW 0 _ _ = const false` etc.
    * `Pointwise`      — pointwise rewriting rule
    * `Bilinear`      — bilinearity in either argument
                        (pointwise variants in `PointwiseBilinear`)

  ## Leibniz identities

    * `Leibniz`        — Leibniz rule generic statement
    * `BasisLeibniz`   — Leibniz on basis elements
    * `LeibnizMid`     — middle-degree variant
    * `Leibniz4Mixed`  — 4-mixed-degree case
    * `LeibnizBzBridge`  — pointwise `bz5_<n>` ↔ `basis 5 <n>` /
                            `Cochain.zero 5 <n>` rewrites at
                            strata `n ∈ {1, 2, 3}`
    * `Leibniz21Final`   — (2, 1)-final form
    * `Leibniz22Final`   — (2, 2)-final form

  ## Algebraic-lift bridges

    * `LeibnizAlgLift`,
      `LeibnizAlgLift21`,
      `LeibnizAlgLift21Alpha`,
      `LeibnizAlgLift22`,
      `LeibnizAlgLift22Alpha` — algebraic-lift forms used by
      `Universal/Prop*`.

  ## Status

  All files included.  PURE pointwise bilinear formulations live
  at `PointwiseBilinear.lean`.
-/
