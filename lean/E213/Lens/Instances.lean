import E213.Lens.Instances.AB
import E213.Lens.Instances.Bool
import E213.Lens.Instances.BoundedContext
import E213.Lens.Instances.Cauchy
import E213.Lens.Instances.CochainEntry
import E213.Lens.Instances.EndpointBehavior
import E213.Lens.Instances.F9
import E213.Lens.Instances.FunctionSpace
import E213.Lens.Instances.Identity
import E213.Lens.Instances.Max
import E213.Lens.Instances.Pair
import E213.Lens.Instances.Parity
import E213.Lens.Instances.Path
import E213.Lens.Instances.PointwiseProjection
import E213.Lens.Instances.Prism
import E213.Lens.Instances.RawMatching
import E213.Lens.Instances.Reach
import E213.Lens.Instances.Subtype
import E213.Lens.Instances.SubtypeClosed
import E213.Lens.Instances.Sum
import E213.Lens.Instances.SumNotCoproduct
import E213.Lens.Instances.SumNotCoproductGeneric
import E213.Lens.Instances.Swap
import E213.Lens.Instances.ZMod6

/-! Spec-as-code entry point for `E213.Lens.Instances`.

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
