import E213.Hypervisor.Lens.Instances.Parity
import E213.Hypervisor.Lens.Instances.Bool

/-!
# Research.ParityXorIncomparable

**Claim**: `parityLens ∥ boolXorLens` (incomparable in the refines
preorder).

- `parityLens`: base_a = base_b = true, combine = xor.
  view = total leaves count mod 2.
- `boolXorLens`: base_a = true, base_b = false, combine = xor.
  view = a-count mod 2 (a = Raw.a leaves).

The two Lenses extract **different information**:
- parityLens: counts all leaves equally (total parity).
- boolXorLens: distinguishes a and b, counting only a-leaves.

## Witnesses

- `parity_not_refines_xor`: Raw.a vs Raw.b — same parity (1),
  different xor view (a-only vs b-only).
- `xor_not_refines_parity`: Raw.a vs rAAA — same xor view (both
  a-odd), different parity (1 vs 4).
-/

namespace E213.Hypervisor.Lens.Instances.ParityXorIncomparable

open E213.Firmware E213.Hypervisor E213.Meta

theorem parity_equates_ab :
    parityLens.view Raw.a = parityLens.view Raw.b := by decide

theorem xor_distinguishes_ab :
    boolXorLens.view Raw.a ≠ boolXorLens.view Raw.b := by decide

/-- parityLens does not refine boolXorLens (loses the a,b distinction). -/
theorem parity_not_refines_xor : ¬ parityLens.refines boolXorLens := by
  intro h
  exact xor_distinguishes_ab (h Raw.a Raw.b parity_equates_ab)

/-- Witness `a / (a / (a/b))` — a-count=3 odd, total-count=4 even. -/
def rAAA : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

theorem xor_equates :
    boolXorLens.view Raw.a = boolXorLens.view rAAA := by decide

theorem parity_distinguishes :
    parityLens.view Raw.a ≠ parityLens.view rAAA := by decide

/-- boolXorLens does not refine parityLens (loses total information). -/
theorem xor_not_refines_parity : ¬ boolXorLens.refines parityLens := by
  intro h
  exact parity_distinguishes (h Raw.a rAAA xor_equates)

end E213.Hypervisor.Lens.Instances.ParityXorIncomparable
