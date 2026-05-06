import E213.Meta.Tactic.VerifyConjugation
import E213.Lib.Math.CayleyDickson.ZIInstance
import E213.Lib.Math.CayleyDickson.Z2Instance
import E213.Lib.Math.CayleyDickson.ZOmegaInstance
import E213.Lib.Math.CayleyDickson.ZSqrtInstance

/-!
# Tests: `#verify_conjugation` scans all six ConjugationCodomain witnesses.

After importing the four Instance modules, `#verify_conjugation`
should succeed for each registered type.  Verifies that
typeclass synthesis reaches every instance.

NB: this file imports the Instance modules which depend
transitively on `Firmware.Raw` (for `Raw.fold_swap_hom`).
Full verification therefore requires the Raw build.
-/

open E213.Tactic
open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZSqrt2
open E213.Lib.Math.CayleyDickson.ZOmega
open E213.Lib.Math.CayleyDickson.ZSqrt

-- Three concrete witnesses
#verify_conjugation ZI
#verify_conjugation Z2
#verify_conjugation ZOmega

-- Three parametric instances
#verify_conjugation (ZSqrt 3)
#verify_conjugation (ZSqrt 5)
#verify_conjugation (ZSqrt 7)
