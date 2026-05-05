import E213.Meta.AxiomMinimality
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.BitPatternUniqueness
import E213.Meta.CUniquenessBridge
import E213.Meta.RawInductionDemo
import E213.Meta.SelfRecognising
import E213.Meta.Tactic.DeriveConjugationCodomain
import E213.Meta.Tactic.NativeGuard
import E213.Meta.Tactic.NativeGuardTest
import E213.Meta.Tactic.PureGuard
import E213.Meta.Tactic.PureGuardTest
import E213.Meta.Tactic.Test.VerifyConjugationTest
import E213.Meta.Tactic.VerifyConjugation
import E213.Meta.Universal.LensClaim
import E213.Meta.Universal.MorphismFactor
import E213.Meta.Universal.Reflection
import E213.Meta.UniversalLens.Core
import E213.Meta.UniversalLens.Nat2
import E213.Meta.UniversalLens.Nat2Inj
import E213.Meta.UniversalLens.Nat3
import E213.Meta.UniversalLens.Nat4
import E213.Meta.UniversalLens.Padding
import E213.Meta.UniversalLens.PaddingCapstone
import E213.Meta.UniversalLens.Q213
import E213.Meta.UniversalLens.Q213Inj
import E213.Meta.UniversalLens.Q213_3
import E213.Meta.UniversalLens.TripleCapstone

/-! Spec-as-code entry point for `E213.Meta` — meta-tier modules.

  Meta layer (Meta/) — reflective primitives that observe and constrain the Hypervisor: AxiomMinimality, BitPatternUniqueness, SelfRecognising, plus the Universal/UniversalLens combinator hierarchy and the meta-level Tactic/ macros (DeriveConjugationCodomain, VerifyConjugation, NativeGuard, PureGuard).

  ## Status

  27 files included.  0 files excluded
  (pre-existing breakage):

    (none)
-/
