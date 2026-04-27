import E213.Meta.ParityLens
import E213.Meta.BoolLens

/-!
# Research.ParityXorIncomparable

**주장**: `parityLens ∥ boolXorLens` (refines preorder 에서
incomparable).

- `parityLens`: base_a = base_b = true, combine = xor.
  view = total leaves count mod 2.
- `boolXorLens`: base_a = true, base_b = false, combine = xor.
  view = a-count mod 2 (a = Raw.a leaves).

두 Lens 는 다른 **정보를 추출**:
- parityLens: 모든 leaf 를 동등하게 센다 (total parity).
- boolXorLens: a 와 b 를 구별하여 a-count 만 센다.

## Witnesses

- `parity_not_refines_xor`: Raw.a vs Raw.b — 같은 parity (1),
  다른 xor view (a-only vs b-only).
- `xor_not_refines_parity`: Raw.a vs rAAA — 같은 xor view
  (둘 다 a-odd), 다른 parity (1 vs 4).
-/

namespace E213.Research.ParityXorIncomparable

open E213.Firmware E213.Hypervisor E213.Meta

theorem parity_equates_ab :
    parityLens.view Raw.a = parityLens.view Raw.b := by decide

theorem xor_distinguishes_ab :
    boolXorLens.view Raw.a ≠ boolXorLens.view Raw.b := by decide

/-- parityLens 는 boolXorLens 를 refine 하지 않음 (a,b 구별 손실). -/
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

/-- boolXorLens 는 parityLens 를 refine 하지 않음 (total 정보 손실). -/
theorem xor_not_refines_parity : ¬ boolXorLens.refines parityLens := by
  intro h
  exact parity_distinguishes (h Raw.a rAAA xor_equates)

end E213.Research.ParityXorIncomparable
