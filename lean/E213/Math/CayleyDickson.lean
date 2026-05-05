import E213.Math.CayleyDickson.CDDouble
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

  16 files included.  13 files excluded
  (Lipschitz/Cayley/Sedenion cascade still has overload ambiguity
  with `ext`/`mul_comm` resolving to multiple namespaces; deferred):

    - CDTower
    - Cayley
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
