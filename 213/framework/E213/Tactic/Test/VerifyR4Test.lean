import E213.Tactic.VerifyR4
import E213.Research.ZIInstance
import E213.Research.Z2Instance
import E213.Research.ZOmegaInstance
import E213.Research.ZSqrtInstance

/-!
# Tests: `#verify_r4` scans all six R4Codomain witnesses.

After importing the four Instance modules, `#verify_r4`
should succeed for each registered type.  Verifies that
typeclass synthesis reaches every instance.

NB: this file imports the Instance modules which depend
transitively on `Firmware.Raw` (for `Raw.fold_swap_hom`).
Full verification therefore requires the Raw build.
-/

open E213.Tactic E213.Research

-- Three concrete witnesses
#verify_r4 ZI
#verify_r4 Z2
#verify_r4 ZOmega

-- Three parametric instances
#verify_r4 (ZSqrt 3)
#verify_r4 (ZSqrt 5)
#verify_r4 (ZSqrt 7)
