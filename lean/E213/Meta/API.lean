import E213.Meta.SelfRecognising
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.Universal
import E213.Meta.UniversalLens

/-! # Meta layer public API

  Single import for downstream consumers.  Bundles the four
  pillars of the framework metatheory:

  ## ME-1 — SelfRecognising codomain hierarchy

  3-tier typeclass extension chain:

    `CommBinaryCodomain → NonVanishingCodomain → ConjugationCodomain`

  Specifies what α-codomains can carry a Lens that satisfies
  successively stronger axiomatic conditions.

  Public names:
    * `CommBinaryCodomain`, `NonVanishingCodomain`, `ConjugationCodomain`
      (typeclasses + instances + generic theorems per tier)

  ## ME-2 — AxiomMinimality

  Proof that the Raw axiom set is irreducible: removing any
  clause collapses the framework.

  Public names:
    * `Meta.AxiomMinimality.*` — 4-case minimality proof
    * `Meta.AxiomMinimalityCapstone.raw_minimality_capstone`

  ## ME-3 — Universal-Lens metatheorems

  "Every framework is a Lens" — formal claim + image
  factorisation + reflection.

  Public names:
    * `Meta.Universal.LensClaim`
    * `Meta.Universal.MorphismFactor`
    * `Meta.Universal.Reflection`

  ## ME-4 — UniversalLens concrete witnesses

  Concrete universal-Lens instances at codomains
  {ℕ², ℕ³, ℕ⁴, Q213, Q213³} + padding theorems +
  triple capstone.

  Public names:
    * `Meta.UniversalLens.Core`
    * `Meta.UniversalLens.{Nat2, Nat3, Nat4}`
    * `Meta.UniversalLens.{Q213, Q213_3}`
    * `Meta.UniversalLens.{Padding, PaddingCapstone}`
    * `Meta.UniversalLens.TripleCapstone`

  ## Optional separate imports (NOT bundled in this shim)

    * `Meta.Tactic` — code-generators + verification
      (`DeriveConjugationCodomain`, `VerifyConjugation`,
      `NativeGuard`, `PureGuard`).  Tactic API is cross-cutting;
      consumers import on demand.

    * `Meta.BitPatternUniqueness`, `Meta.RawInductionDemo`,
      `Meta.CUniquenessBridge` — supporting lemmas used by ME-2/4
      but not part of the stable surface.

  ## Layered position

  Imports `Lens` (uses Lens type for `specLens` constructions).
  Sits above Lens and below Lib in the ring model.
-/
