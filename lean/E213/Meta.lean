import E213.Meta.AxiomMinimality
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.BitPatternUniqueness
import E213.Meta.LensInternality
import E213.Meta.SelfRecognising
import E213.Meta.Tactic
import E213.Meta.UniversalLens

/-! Spec-as-code entry point for `E213.Meta`.

  Meta layer — reflective primitives that observe and constrain
  the Lens framework.

  ## Top-level modules

    * `AxiomMinimality`,
      `AxiomMinimalityCapstone` — minimality of the 213 axiom set
    * `BitPatternUniqueness`    — bit-pattern uniqueness witness
    * `LensInternality`         — Lens is a Raw-internal concept
                                  (data triple + Raw.fold view)
    * `SelfRecognising`         — 3-tier codomain typeclass hierarchy
                                  (`CommBinaryCodomain`,
                                  `NonVanishingCodomain`,
                                  `ConjugationCodomain`)

  ## Sub-cluster umbrellas

    * `Tactic/`        — meta-level tactics (DeriveConjugationCodomain,
                         VerifyConjugation, NativeGuard, PureGuard
                         + Test/)
    * `UniversalLens/` — Q213 / Nat2 / Nat3 / Nat4 / Padding /
                         Triple capstones
-/
