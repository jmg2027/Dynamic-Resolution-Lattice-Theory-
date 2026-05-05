import E213.Math.CayleyDickson.F2CDTower
import E213.Math.CayleyDickson.ZI
import E213.Math.CayleyDickson.ZIArith
import E213.Math.CayleyDickson.ZIDomain
import E213.Math.CayleyDickson.ZIHom
import E213.Math.CayleyDickson.ZOmega
import E213.Math.CayleyDickson.ZOmegaDomain
import E213.Math.CayleyDickson.ZSqrt
import E213.Math.CayleyDickson.ZSqrt2
import E213.Math.CayleyDickson.ZSqrt2Domain
import E213.Math.CayleyDickson.ZSqrtDomain

/-! Spec-as-code entry point for `E213.Math.CayleyDickson` —
  Cayley-Dickson construction (octonion / sedenion / quaternion-style
  algebras over 213).

  ## Status

  11 files included.  18 files excluded (pre-existing
  breakage requires surgical archaeology — the namespace structure
  uses doubled `ZI.ZI.*` paths and the `derive_conjugation_codomain`
  tactic generates code expecting Z2/ZSqrt theorems in the type's
  namespace, but they currently live in separate `*Domain` files):

    - CDDouble
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
    - Z2Instance
    - ZIInstance
    - ZOmegaInstance
    - ZSqrtInstance
    - ZSqrtProduct
-/
