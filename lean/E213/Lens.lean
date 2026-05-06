import E213.Lens.API
import E213.Lens.LensCore
import E213.Lens.AxiomLenses.Bridges
import E213.Lens.AxiomLenses.Core
import E213.Lens.Characterisation
import E213.Lens.Compose
import E213.Lens.Initiality
import E213.Lens.Instances
import E213.Lens.Algebra
import E213.Lens.Lattice
import E213.Lens.Leaves
import E213.Lens.Morphism
import E213.Lens.Properties
import E213.Lens.Refines
import E213.Lens.SemanticAtom
import E213.Lens.Universal

/-! Spec-as-code entry point for `E213.Lens`.

  Hypervisor layer — the Lens algebra.

  ## Chapters (sub-cluster umbrellas)

    * `Lens.AxiomLenses.{Bridges, Core}` — axiom-lens family
      (Funext / Propext / QuotSound)
    * `Lens.Characterisation`            — Catalog + Core
    * `Lens.Compose`                     — composition operators
      (Factoring, OnLens, ImageMinimum, Morphism, OnLensImage*)
    * `Lens.Instances`                   — concrete Lens instances
      (AB, Bool, Cauchy, Path, Prism, Reach, Subtype, Sum, Swap,
       ZMod6, …)
    * `Lens.Kernel`                      — algebraic kernel
      (CardinalityLB, Congruence, Corresp, FourDistinct, FreeAudit,
       IdLensEq, Space, SwapInvariant)
    * `Lens.Lattice`                     — join/meet (Family*,
      Indexed, Join, JoinEquiv, Lattice, Meet)
    * `Lens.Leaves`                      — depth-leaf hierarchy
      (DepthIncomparable, DepthJoin, Mod3, ModNat, RefinesParity)
    * `Lens.Morphism`                    — morphism shape catalogue
    * `Lens.Properties`                  — derived predicates
    * `Lens.Refines`                     — refines preorder
    * `Lens.Universal`                   — Universal flat / quot lens

  ## Top-level

    * `API.lean`            — public surface
    * `Lens.lean`           — Lens type + view/equiv
    * `Lens/Initiality.lean`    — initiality of the Lens category
    * `Lens/SemanticAtom.lean`  — semantic-atom characterisation

  ## Status

  Pre-existing API drift on 10 files documented in
  `research-notes/HIERARCHICAL_PLACEMENT.md` §6.1.  Each
  sub-cluster umbrella records its own deferred list inline.
-/
