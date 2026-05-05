import E213.Math.CayleyDickson.CDDouble
import E213.Math.CayleyDickson.Cayley
import E213.Math.CayleyDickson.F2CDTower
import E213.Math.CayleyDickson.Z2Instance
import E213.Math.CayleyDickson.ZI
import E213.Math.CayleyDickson.ZIArith
import E213.Math.CayleyDickson.ZIDomain
import E213.Math.CayleyDickson.ZIHom
import E213.Math.CayleyDickson.ZIInstance
import E213.Math.CayleyDickson.ZOmega
import E213.Math.CayleyDickson.ZOmegaDomain
import E213.Math.CayleyDickson.ZOmegaInstance
import E213.Math.CayleyDickson.ZSqrt
import E213.Math.CayleyDickson.ZSqrt2
import E213.Math.CayleyDickson.ZSqrt2Domain
import E213.Math.CayleyDickson.ZSqrtDomain
import E213.Math.CayleyDickson.ZSqrtInstance

/-! Spec-as-code entry point for `E213.Math.CayleyDickson` —
  Cayley-Dickson construction over 213.

  ## Status

  17 files included.  12 files excluded
  (cascade still has minor issues — wrong-path qualifications
  inserted by bulk regex, plus `decide` failures on combinator-
  derived expressions; deferred):

    - CDTower
    - CayleyHeavy
    - LipschitzHeavy
    - LipschitzLens
    - Pathion
    - PathionHeavy
    - R5Vacuity
    - Sedenion
    - SedenionHeavy
    - TrigintaduoionionHeavy
    - Trigintaduonion
    - ZSqrtProduct
-/
