import E213.Lens.API
import E213.Lens.LensCore
import E213.Lens.AxiomLenses
import E213.Lens.Compose
import E213.Lens.Initiality
import E213.Lens.Instances
import E213.Lens.Algebra
import E213.Lens.Cardinality
import E213.Lens.Lattice
import E213.Lens.Number
import E213.Lens.Properties
import E213.Lens.SemanticAtom
import E213.Lens.Universal

/-! Spec-as-code entry point for `E213.Lens`.

  Lens layer — the Lens algebra.

  ## Chapters (sub-cluster umbrellas)

    * `Lens.AxiomLenses.{Bridges, Core}` — axiom-lens family
      (Funext / Propext / QuotSound)
    * `Lens.Compose`                     — composition operators
      (Factoring, OnLens, ImageMinimum, Morphism, OnLensImage*)
    * `Lens.Instances`                   — concrete Lens instances
      (AB, Bool, Cauchy, Path, Prism, Reach, Subtype, Sum, Swap,
       ZMod6, …) + `Leaves/` sub-cluster (Mod3, ModNat, DepthJoin,
      DepthIncomparable, RefinesParity) — 2026-05-13 폴드
    * `Lens.Algebra`                     — algebraic kernel
      (Congruence, Corresp, FourDistinct, FreeAudit, IdLensEq,
       Space, SwapInvariant)
    * `Lens.Cardinality`                 — cardinality observables
      (Cantor, Tower, BoolSpace, Countable, Pair, Godel, Chain,
       LensCardinality, CardinalityLB) — moved 2026-05-13 from
      Lib/Math/Infinity + Lens/Algebra
    * `Lens.Lattice`                     — refines preorder
      (Chain, Preorder) + lattice (Join, Meet, JoinEquiv,
       IndexedJoin, FamilyJoin/Meet) — Refines 폴드 2026-05-13
    * `Lens.Properties`                  — derived predicates +
      `Diagonal` (sq classification: Collapse/Idempotent/Escalate/
      Multiply) + `Characterisation/` (Catalog + Core) +
      `Morphism/` (8 files: FoldStructured, BoolProp, Dist,
      SlashSwap, NoDepthParity, DepthParityNotFold, SlashCharNotFold,
      BoolSqClassification) — 2026-05-13 폴드
    * `Lens.Number`                      — Raw-derived number systems
      (Nat213 — Raw chain + Peano inductive + Bridge + Lenses +
       NumberingSystem + RawCut + Tower).  Migrated 2026-05-14 from
      `Theory.Closed.{Nat213, Nat213Bridge, RawCut, NumberingSystem}`
      + `Theory.Nat213.*` + `Theory.Tower.NatPairToQPos` — each one
      is a `Raw.fold`-catamorphism artifact, hence Lens-layer.
    * `Lens.Universal`                   — Universal flat / quot lens
                                            + `Witnesses/`

  ## Top-level

    * `API.lean`            — public surface
    * `Lens.lean`           — Lens type + view/equiv
    * `Lens/Initiality.lean`    — initiality of the Lens category
    * `Lens/SemanticAtom.lean`  — semantic-atom characterisation

  ## Status

  Post-M14 deferred-cluster repair complete: all formerly-deferred
  10 files (CompoundBool, NegSq, ParityXorIncomparable,
  ParityXorJoin, RawAChar, BoolSqClassification, SlashCharNotFold,
  ABRefines, Leaf, ParityCollapseFalse) restored.  `Diagonal.lean`
  added to host the Collapse/Idempotent classification predicates
  (formerly in deleted `Math.Diagonal.Classification`).
-/
