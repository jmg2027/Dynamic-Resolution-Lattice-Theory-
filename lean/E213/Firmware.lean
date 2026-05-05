import E213.Firmware.Atomicity
import E213.Firmware.Atomicity.Alive
import E213.Firmware.Atomicity.ArityForcing
import E213.Firmware.Atomicity.ArityForcingGeneral
import E213.Firmware.Atomicity.Five
import E213.Firmware.Atomicity.FiveHelpers
import E213.Firmware.Atomicity.NonDecomposable
import E213.Firmware.Atomicity.PairForcing
import E213.Firmware.Atomicity.PrimitiveSizes
import E213.Firmware.Raw
import E213.Firmware.Raw.Cmp
import E213.Firmware.Raw.CmpIndependence
import E213.Firmware.Raw.ComplexityClass
import E213.Firmware.Raw.Core
import E213.Firmware.Raw.DecEq
import E213.Firmware.Raw.Fold
import E213.Firmware.Raw.Hom
import E213.Firmware.Raw.Levels
import E213.Firmware.Raw.Rec
import E213.Firmware.Raw.Signed
import E213.Firmware.Raw.Slash
import E213.Firmware.Raw.Swap
import E213.Firmware.Raw.SwapSlash
import E213.Firmware.Raw.SwapSlashInjective
import E213.Firmware.RawLevels
import E213.Firmware.RawSwap
import E213.Firmware.Tools.CertChecker

/-! Spec-as-code entry point for `E213.Firmware` — firmware-tier modules.

  Firmware layer (Firmware/) — bridges between the type-theoretic Kernel and the operator-level Hypervisor.  Hosts the canonical Raw monad, fold/swap homomorphism scaffolding, and the deduction primitives consumed by Hypervisor lenses.

  ## Status

  27 files included.  0 files excluded
  (pre-existing breakage):

    (none)
-/
