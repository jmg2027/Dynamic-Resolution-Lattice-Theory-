import E213.Theory.Atomicity
import E213.Theory.Raw
import E213.Theory.RawLevels
import E213.Theory.RawSwap
import E213.Theory.Tools.CertChecker

/-! Spec-as-code entry point for `E213.Theory`.

  Firmware layer — bridges between the type-theoretic Kernel and
  the operator-level Hypervisor.  Hosts the canonical Raw monad,
  fold / swap homomorphism scaffolding, and the deduction
  primitives consumed by Hypervisor lenses.

  ## Sub-clusters

    * `Atomicity/`  — atomicity-forcing module (Alive,
                      ArityForcing*, Five, FiveHelpers,
                      NonDecomposable, PairForcing,
                      PrimitiveSizes)
    * `Raw/`        — Raw monad core (Core, Cmp, CmpIndependence,
                      ComplexityClass, DecEq, Fold, Hom, Levels,
                      Rec, Signed, Slash, Swap, SwapSlash,
                      SwapSlashInjective)

  ## Top-level

    * `Raw.lean`              — Raw cluster entry
    * `RawLevels`             — Raw-level annotations
    * `RawSwap`               — top-level swap operator
    * `Tools/CertChecker`     — certificate-checking utility
-/
