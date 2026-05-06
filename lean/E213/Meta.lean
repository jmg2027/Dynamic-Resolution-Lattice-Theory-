import E213.Meta.AxiomMinimality
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.BitPatternUniqueness
import E213.Meta.CUniquenessBridge
import E213.Meta.RawInductionDemo
import E213.Meta.SelfRecognising
import E213.Meta.Tactic
import E213.Meta.Universal
import E213.Meta.UniversalLens

/-! Spec-as-code entry point for `E213.Meta`.

  Meta layer — reflective primitives that observe and constrain
  the Hypervisor.

  ## Top-level modules

    * `AxiomMinimality`,
      `AxiomMinimalityCapstone` — minimality of the 213 axiom set
    * `BitPatternUniqueness`    — bit-pattern uniqueness witness
    * `CUniquenessBridge`       — constant-uniqueness bridge
    * `RawInductionDemo`        — Raw induction demonstration
    * `SelfRecognising`         — 3-tier codomain typeclass hierarchy
                                  (`CommBinaryCodomain`,
                                  `NonVanishingCodomain`,
                                  `ConjugationCodomain`)

  ## Sub-cluster umbrellas

    * `Tactic/`        — meta-level tactics (DeriveConjugationCodomain,
                         VerifyConjugation, NativeGuard, PureGuard
                         + Test/)
    * `Universal/`     — universal-Lens metatheorems
                         (LensClaim, MorphismFactor, Reflection)
    * `UniversalLens/` — Q213 / Nat2 / Nat3 / Nat4 / Padding /
                         Triple capstones
-/
