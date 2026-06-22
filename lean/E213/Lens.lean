import E213.Lens.API
import E213.Lens.LensCore
import E213.Lens.ReadingEquiv
import E213.Lens.AxiomLenses
import E213.Lens.Bool213
import E213.Lens.Compose
import E213.Lens.Congruence
import E213.Lens.Foundations.FlatOntology
import E213.Lens.Foundations.Initiality
import E213.Lens.Foundations.PredicateSelfEncoding
import E213.Lens.Foundations.NoExteriorClosure
import E213.Lens.ProofISA
import E213.Lens.ProofISADemo
import E213.Lens.Foundations.ResidueReentry
import E213.Lens.Foundations.OneDiagonal
import E213.Lens.Foundations.UniversalDistinguishing
import E213.Lens.RawTopology
import E213.Lens.SelfCompletion
import E213.Lens.SelfReferenceThreeOutcomes
import E213.Lens.Instances
import E213.Lens.Algebra
import E213.Lens.Cardinality
import E213.Lens.DirectionFree
import E213.Lens.Lattice
import E213.Lens.Number
import E213.Lens.Properties
import E213.Lens.Foundations.SemanticAtom
import E213.Lens.SyntacticInternalization
import E213.Lens.Unified
import E213.Lens.Universal
import E213.Lens.Number.Founding

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
      DepthIncomparable, RefinesParity)
    * `Lens.Algebra`                     — algebraic kernel
      (Congruence, Corresp, FourDistinct, FreeAudit, IdLensEq,
       Space, SwapInvariant)
    * `Lens.Cardinality`                 — cardinality observables
      (Cantor, Tower, BoolSpace, Countable, Pair, Godel, Chain,
       LensCardinality, CardinalityLB) 
    * `Lens.Lattice`                     — refines preorder
      (Chain, Preorder) + lattice (Join, Meet, JoinEquiv,
       IndexedJoin, FamilyJoin/Meet)
    * `Lens.Properties`                  — derived predicates +
      `Diagonal` (sq classification: Collapse/Idempotent/Escalate/
      Multiply) + `Characterisation/` (Catalog + Core) +
      `Morphism/` (8 files: FoldStructured, BoolProp, Dist,
      SlashSwap, NoDepthParity, DepthParityNotFold, SlashCharNotFold,
      BoolSqClassification)
    * `Lens.Number`                      — Raw-derived number systems
      (Nat213 — Raw chain + Peano inductive + Bridge + Lenses +
       NumberingSystem + RawCut + Tower).
      + `Theory.Nat213.*` + `Theory.Tower.NatPairToQPos` — each one
      is a `Raw.fold`-catamorphism artifact, hence Lens-layer.
    * `Lens.Bool213`                     — Raw-encoded closed-universe
      Bool (Raw — Method A T=a, F=b, + System — (T,F) 메타 패턴).
      `booleanProj := Raw.fold T F and` 의 catamorphism output.

      (scope C, same Lens-layer principle as Nat213).
    * `Lens.Universal`                   — Universal flat / quot lens
                                            + `Witnesses/`
    * `Lens.Congruence`                  — Bridge between `Eqv`
      (internal generic equivalence closure, see `Theory.Raw.
      Congruence`) and `Lens.equiv` (external view equality);
      `Eqv L.equiv ↔ L.equiv` biconditional for any lens.
.
    * `Lens.SyntacticInternalization`    — §9.4 syntactic
      internalisation prototype: 7-glyph alphabet (`a, b, /, (, ),
      `,`, whitespace`) Raw-encoded; Polish-prefix printer + parser
      + universal round-trip `∀ t, parseTree (printTree t) = some t`
      (21 strict ∅-axiom).
    * `Lens.Foundations.FlatOntology`     — §9.3 flat-ontology
      realisation: objects, types, relations, functions, and Lens
      all as decidable predicates on Raw^n.
    * `Lens.Foundations.PredicateSelfEncoding` — §9.3 closure (predicates
      back to Raw via positional truth-table Gödel numbering).
      Closes the self-reference loop: predicates that operate on
      Raw are themselves Raw.
    * `Lens.RawTopology`                  — §9.5 K_∞ ≡ point
      bookend (constLens collapses Raw to a singleton) plus
      the discrete bookend (idLens kernel = equality), bundled
      as the two endpoints of the Lens-refinement lattice.

  ## Top-level

    * `API.lean`            — public surface
    * `Lens.lean`           — Lens type + view/equiv
    * `Lens/Foundations/Initiality.lean`    — initiality of the Lens category
    * `Lens/Foundations/SemanticAtom.lean`  — semantic-atom characterisation
    * `Lens/Congruence.lean`    — `Eqv ↔ L.equiv` bridge
    * `Lens/SyntacticInternalization.lean` — glyph-as-Raw L2 + L3
                                              round-trip

  ## Status

  All cluster files build clean.  `Diagonal.lean` hosts the
  Collapse / Idempotent classification predicates.
-/
