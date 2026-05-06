import E213.Hypervisor.Instances.AB
import E213.Hypervisor.Instances.Bool
import E213.Hypervisor.Instances.BoundedContext
import E213.Hypervisor.Instances.Cauchy
import E213.Hypervisor.Instances.CochainEntry
import E213.Hypervisor.Instances.EndpointBehavior
import E213.Hypervisor.Instances.F9
import E213.Hypervisor.Instances.FunctionSpace
import E213.Hypervisor.Instances.Identity
import E213.Hypervisor.Instances.Max
import E213.Hypervisor.Instances.Pair
import E213.Hypervisor.Instances.Parity
import E213.Hypervisor.Instances.Path
import E213.Hypervisor.Instances.PointwiseProjection
import E213.Hypervisor.Instances.Prism
import E213.Hypervisor.Instances.RawMatching
import E213.Hypervisor.Instances.Reach
import E213.Hypervisor.Instances.Subtype
import E213.Hypervisor.Instances.SubtypeClosed
import E213.Hypervisor.Instances.Sum
import E213.Hypervisor.Instances.SumNotCoproduct
import E213.Hypervisor.Instances.SumNotCoproductGeneric
import E213.Hypervisor.Instances.Swap
import E213.Hypervisor.Instances.ZMod6

/-! Spec-as-code entry point for `E213.Hypervisor.Instances`.

  Catalogue of concrete `Lens` instances over Raw.  Importing
  this module gives access to every clean instance witness.

  ## Per-codomain instances

    * `AB`            — abLens : Lens (Nat × Nat) (a-count, b-count)
    * `Bool`          — boolXorLens / parityLens
    * `Identity`      — id-Lens
    * `Pair`          — Lens of pair-of-Lenses
    * `Sum`           — disjoint-union Lens
    * `Subtype`,
      `SubtypeClosed` — Subtype-restricted Lens
    * `Cauchy`        — Cauchy-decision Lens (used by
                        `Math.Cauchy.ProfiniteSeq`)
    * `Path`          — path-Lens
    * `Prism`         — prism-shape Lens
    * `Reach`         — reachability Lens
    * `Swap`,
      `RawMatching`   — swap-symmetric Lenses
    * `Parity`        — Bool-parity
    * `Max`           — max-Lens
    * `BoundedContext`,
      `EndpointBehavior`,
      `CochainEntry`,
      `F9`,
      `FunctionSpace`,
      `PointwiseProjection`,
      `SumNotCoproduct`,
      `SumNotCoproductGeneric`,
      `ZMod6`         — additional research-track instances

  ## Status

  24/29 instances build clean.  Five deferred (pre-existing
  API drift): `CompoundBool`, `NegSq`, `ParityXorIncomparable`,
  `ParityXorJoin`, `RawAChar`.  See
  `research-notes/HIERARCHICAL_PLACEMENT.md` §6.1.
-/
