import E213.Lens.Instances.AB
import E213.Lens.Instances.Bool
import E213.Lens.Instances.BoundedContext
import E213.Lens.Instances.Cauchy
import E213.Lens.Instances.CochainEntry
import E213.Lens.Instances.CompoundBool
import E213.Lens.Instances.EndpointBehavior
import E213.Lens.Instances.F9
import E213.Lens.Instances.FunctionSpace
import E213.Lens.Instances.Identity
import E213.Lens.Instances.Max
import E213.Lens.Instances.NegSq
import E213.Lens.Instances.Pair
import E213.Lens.Instances.Parity
import E213.Lens.Instances.ParityXorIncomparable
import E213.Lens.Instances.ParityXorJoin
import E213.Lens.Instances.Path
import E213.Lens.Instances.PointwiseProjection
import E213.Lens.Instances.Prism
import E213.Lens.Instances.RawAChar
import E213.Lens.Instances.RawMatching
import E213.Lens.Instances.Reach
import E213.Lens.Instances.Subtype
import E213.Lens.Instances.SubtypeClosed
import E213.Lens.Instances.Sum
import E213.Lens.Instances.SumNotCoproduct
import E213.Lens.Instances.SumNotCoproductGeneric
import E213.Lens.Instances.Swap
import E213.Lens.Instances.ZMod6
import E213.Lens.Instances.Leaves

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
    * `Leaves/`       — depth-leaf hierarchy sub-cluster
                        (Mod3, ModNat, DepthJoin, DepthIncomparable,
                         RefinesParity) — 2026-05-13 folded from
                        `Lens/Leaves/` per LENS_AUDIT §4

  ## Status

  All 29 instances build clean (post-M14 deferred-cluster repair):
  `CompoundBool`, `NegSq`, `ParityXorIncomparable`, `ParityXorJoin`,
  `RawAChar` restored by namespace-drift fixes
  (`open E213.Meta` → `open E213.Lens.Instances.{Bool,Parity}`,
  `Lens` → `Lens`, and re-routing `NegSq` through
  `E213.Lens.Properties.Diagonal`).
-/
