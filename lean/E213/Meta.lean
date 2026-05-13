import E213.Meta.Algebra213
import E213.Meta.AxiomMinimality
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.BitPatternUniqueness
import E213.Meta.Int213
import E213.Meta.LensInternality
import E213.Meta.Nat
import E213.Meta.SelfRecognising
import E213.Meta.Tactic

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
                         (구 Lib/Math/NatHelpers, 2026-05-13)
    * `Int213/`,
      `Algebra213/`    — ring-independent integer / algebra
                         scaffolding

  UniversalLens 11 파일 (Core, Nat2, Nat2Inj, Nat3, Nat4, Padding,
  PaddingCapstone, Q213, Q213Inj, Q213_3, TripleCapstone) 는
  2026-05-13 `Lens/Universal/Witnesses/` 로 이동 — Lens-content 가
  Meta 에 misshoused 된 상태였음을 LENS_AUDIT §4 가 지적.
-/
