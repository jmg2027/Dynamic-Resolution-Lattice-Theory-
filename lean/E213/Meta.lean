import E213.Meta.Algebra213
import E213.Meta.AxiomMinimality
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.BitPatternUniqueness
import E213.Meta.Int213
import E213.Meta.LensInternality
import E213.Meta.Nat
import E213.Meta.OrderWrap
import E213.Meta.OrbitIsIter
import E213.Meta.SelfRecognising
import E213.Meta.Tactic
import E213.Meta.ThreeDirectionUniqueness
import E213.Meta.API

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
    * `Nat/`           — ring-independent Nat helper lemmas
                        
    * `Int213/`,
      `Algebra213/`    — ring-independent integer / algebra
                         scaffolding

  The 11 UniversalLens files (Core, Nat2, Nat2Inj, Nat3, Nat4,
  Padding, PaddingCapstone, Q213, Q213Inj, Q213_3, TripleCapstone)
  were relocated to `Lens/Universal/Witnesses/` —
  LENS_AUDIT §4 noted that the Lens content had been misshoused
  in Meta.
-/
