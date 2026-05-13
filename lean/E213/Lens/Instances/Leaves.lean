import E213.Lens.Instances.Leaves.DepthIncomparable
import E213.Lens.Instances.Leaves.DepthJoin
import E213.Lens.Instances.Leaves.Mod3
import E213.Lens.Instances.Leaves.ModNat
import E213.Lens.Instances.Leaves.RefinesParity

/-! Sub-cluster aggregator for `E213.Lens.Instances.Leaves`.

  Depth-leaf hierarchy: a specific Lens family at the bottom of
  the refines preorder.  Catalogued under `Instances/` since
  these are concrete Lens witnesses (folded into Instances/
  2026-05-13 per LENS_AUDIT §4).

  ## Files (5)

    * `Mod3`              — mod-3 leaf
    * `ModNat`            — generic mod-N leaf family
    * `RefinesParity`     — parity-refinement witness
    * `DepthJoin`         — join of depth-comparable leaves
    * `DepthIncomparable` — depth-incomparable witness
-/
