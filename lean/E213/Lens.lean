import E213.Lens.API
import E213.Lens.LensCore
import E213.Lens.AxiomLenses.Bridges
import E213.Lens.AxiomLenses.Core
import E213.Lens.Characterisation
import E213.Lens.Compose
import E213.Lens.Diagonal
import E213.Lens.Initiality
import E213.Lens.Instances
import E213.Lens.Algebra
import E213.Lens.Cardinality
import E213.Lens.Lattice
import E213.Lens.Morphism
import E213.Lens.Properties
import E213.Lens.SemanticAtom
import E213.Lens.Universal

/-! Spec-as-code entry point for `E213.Lens`.

  Lens layer — the Lens algebra.

  ## Chapters (sub-cluster umbrellas)

    * `Lens.AxiomLenses.{Bridges, Core}` — axiom-lens family
      (Funext / Propext / QuotSound)
    * `Lens.Characterisation`            — Catalog + Core
    * `Lens.Compose`                     — composition operators
      (Factoring, OnLens, ImageMinimum, Morphism, OnLensImage*)
    * `Lens.Diagonal`                    — diagonal (sq) classification
      (Collapse / Idempotent / Escalate / Multiply over Bool, Nat, F9)
    * `Lens.Instances`                   — concrete Lens instances
      (AB, Bool, Cauchy, Path, Prism, Reach, Subtype, Sum, Swap,
       ZMod6, …)
    * `Lens.Kernel`                      — algebraic kernel
      (Congruence, Corresp, FourDistinct, FreeAudit, IdLensEq,
       Space, SwapInvariant)
    * `Lens.Cardinality`                 — cardinality observables
      (Cantor, Tower, BoolSpace, Countable, Pair, Godel, Chain,
       LensCardinality, CardinalityLB) — moved 2026-05-13 from
      Lib/Math/Infinity + Lens/Algebra
    * `Lens.Lattice`                     — join/meet (Family*,
      Indexed, Join, JoinEquiv, Lattice, Meet)
    * `Lens.Instances.Leaves`            — depth-leaf hierarchy
      sub-cluster (Mod3, ModNat, DepthJoin, DepthIncomparable,
      RefinesParity) — 2026-05-13 폴드 from `Lens/Leaves/`
    * `Lens.Morphism`                    — morphism shape catalogue
    * `Lens.Properties`                  — derived predicates
    * (`Lens.Refines` folded into `Lens.Lattice` 2026-05-13 — preorder
       is a Lattice prerequisite, Chain/Preorder now live there)
    * `Lens.Universal`                   — Universal flat / quot lens

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
