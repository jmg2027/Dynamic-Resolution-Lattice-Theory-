import E213.Meta.SelfRecognising
import E213.Meta.AxiomMinimalityCapstone
import E213.Meta.LensInternality

/-! # Meta layer public API

  Single import for downstream consumers.  Bundles the three
  formal pillars of the framework metatheory:

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

  ## ME-3 — LensInternality

  The 213-internal counterpart of "every framework is a Lens": every
  Lens is structurally a triple `(base_a, base_b, combine) ∈ α³`,
  and its view is exactly `Raw.fold` of that triple.  Lens is not
  imported from outside Raw; it is the canonical name for the α-side
  data needed to fold Raw.

  Public names:
    * `Meta.LensInternality.{toData, ofData}`
    * `Meta.LensInternality.{toData_ofData, ofData_toData}`
      (round-trip)
    * `Meta.LensInternality.view_eq_fold`
    * `Meta.LensInternality.lens_is_raw_internal` (∅-axiom capstone)

  ## Optional separate imports (NOT bundled in this shim)

    * `Meta.Tactic` — code-generators + verification
      (`DeriveConjugationCodomain`, `VerifyConjugation`,
      `NativeGuard`, `PureGuard`).  Tactic API is cross-cutting;
      consumers import on demand.

    * `Meta.BitPatternUniqueness` — supporting lemma used by
      `Lens.Universal.Witnesses.Nat2Inj`; not part of the stable
      surface.

    * `Lens.Universal.Witnesses` — concrete universal-Lens instances
      at codomains {ℕ², ℕ³, ℕ⁴, Q213, Q213³} + padding + triple
      capstone.  Moved out of Meta 2026-05-13 (LENS_AUDIT §4):
      Lens-content, not ring-independent Meta.

  ## Adjacent (NOT in this Meta cluster)

    * `Lens/Initiality.lean::Lens.initiality` — categorical universality
      of `Raw.fold` (∃! Raw → α homomorphism per Lens).  Sealed
      `Quot.sound`-dependent (Raw.fold quotient lifting); paired with
      `LensInternality` it gives the full picture but stays in the
      Lens layer rather than Meta.

  ## Layered position

  Imports `Lens` (uses Lens type for `specLens` constructions).
  Sits above Lens and below Lib in the ring model.
-/
