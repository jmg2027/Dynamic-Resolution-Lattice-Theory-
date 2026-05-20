import E213.Lens.API
import E213.Lens.LensCore
import E213.Lens.AxiomLenses
import E213.Lens.Bool213
import E213.Lens.Compose
import E213.Lens.Congruence
import E213.Lens.FlatOntology
import E213.Lens.Initiality
import E213.Lens.PredicateSelfEncoding
import E213.Lens.Instances
import E213.Lens.Algebra
import E213.Lens.Cardinality
import E213.Lens.Lattice
import E213.Lens.Number
import E213.Lens.Properties
import E213.Lens.SemanticAtom
import E213.Lens.SyntacticInternalization
import E213.Lens.UndifferentiatedRaw
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
    * `Lens.Bool213`                     — Raw-encoded closed-universe
      Bool (Raw — Method A T=a, F=b, + System — (T,F) 메타 패턴).
      `booleanProj := Raw.fold T F and` 의 catamorphism output.
      Migrated 2026-05-14 from `Theory.Closed.{Bool213, Bool213System}`
      (scope C, same Lens-layer principle as Nat213).
    * `Lens.Universal`                   — Universal flat / quot lens
                                            + `Witnesses/`
    * `Lens.Congruence`                  — Bridge between `Eqv`
      (internal generic equivalence closure, see `Theory.Raw.
      Congruence`) and `Lens.equiv` (external view equality);
      `Eqv L.equiv ↔ L.equiv` biconditional for any lens.
      Added 2026-05-18 (Option E of the lens-emergence roadmap).
    * `Lens.SyntacticInternalization`    — §9.4 syntactic
      internalisation prototype: 7-glyph alphabet (`a, b, /, (, ),
      `,`, whitespace`) Raw-encoded; Polish-prefix printer + parser
      + universal round-trip `∀ t, parseTree (printTree t) = some t`
      (21 strict ∅-axiom).
    * `Lens.FlatOntology`                 — §9.3 flat-ontology
      realisation: objects, types, relations, functions, and Lens
      all as decidable predicates on Raw^n.
    * `Lens.PredicateSelfEncoding`        — §9.3 closure (predicates
      back to Raw via positional truth-table Gödel numbering).
      Closes the self-reference loop: predicates that operate on
      Raw are themselves Raw.
    * `Lens.UndifferentiatedRaw`          — §9.5 K_∞ ≡ point at
      raw level realised as constant-Lens collapse: under
      `constLens e`, every Raw maps to `e` — the no-distinction
      reading of Raw is a singleton.

  ## Top-level

    * `API.lean`            — public surface
    * `Lens.lean`           — Lens type + view/equiv
    * `Lens/Initiality.lean`    — initiality of the Lens category
    * `Lens/SemanticAtom.lean`  — semantic-atom characterisation
    * `Lens/Congruence.lean`    — `Eqv ↔ L.equiv` bridge (2026-05-18)
    * `Lens/SyntacticInternalization.lean` — glyph-as-Raw L2 + L3
                                              round-trip (2026-05-18)

  ## Status

  Post-M14 deferred-cluster repair complete: all formerly-deferred
  10 files (CompoundBool, NegSq, ParityXorIncomparable,
  ParityXorJoin, RawAChar, BoolSqClassification, SlashCharNotFold,
  ABRefines, Leaf, ParityCollapseFalse) restored.  `Diagonal.lean`
  added to host the Collapse/Idempotent classification predicates
  (formerly in deleted `Math.Diagonal.Classification`).
-/
