import E213.Research.LeavesMod3
import E213.Research.LeavesRefinesParity

/-!
# Research.Mod2Mod3Incomparable

**주장**: `parityLens ∥ leavesMod3Lens` — mod 2 와 mod 3 kernel 은
incomparable.

일반적으로 mod m 과 mod k 가 coprime 이면 둘 kernel 은
incomparable.  이는 Lens kernel 공간이 **최소 countable
무한 chain 이 아니라 antichain** 을 포함함을 보임.

## Witnesses

- `Raw.a` (leaves=1): parity=odd, mod 3=1.
- `r2` = `a/b` (leaves=2): parity=even, mod 3=2.
- `r5` = a/(a/(a/(a/b))) (leaves=5): parity=odd, mod 3=2.

- `Raw.a vs r5`: same parity (odd), different mod 3 (1 vs 2).
- `r2 vs r5`: same mod 3 (2), different parity (even vs odd).
-/

namespace E213.Research.Mod2Mod3Incomparable

open E213.Firmware E213.Hypervisor E213.Meta
open E213.Research.LeavesMod3

/-- Raw with leaves 2. -/
def r2 : Raw := Raw.slash Raw.a Raw.b (by decide)

/-- Raw with leaves 5: `a/(a/(a/(a/b)))`. -/
def r5 : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.a
      (Raw.slash Raw.a
        (Raw.slash Raw.a Raw.b (by decide))
        (by decide))
      (by decide))
    (by decide)

theorem r5_leaves : Lens.leaves.view r5 = 5 := by decide

/-- Raw.a vs r5: same parity (both odd). -/
theorem parity_equates_a_r5 : parityLens.view Raw.a = parityLens.view r5 := by
  decide

/-- Raw.a vs r5: different mod 3 (1 vs 2). -/
theorem mod3_distinguishes_a_r5 :
    leavesMod3Lens.view Raw.a ≠ leavesMod3Lens.view r5 := by decide

/-- **parityLens 는 leavesMod3Lens 를 refine 하지 않음**. -/
theorem parity_not_refines_mod3 :
    ¬ parityLens.refines leavesMod3Lens := by
  intro h
  exact mod3_distinguishes_a_r5 (h Raw.a r5 parity_equates_a_r5)

/-- r2 vs r5: same mod 3 (both 2). -/
theorem mod3_equates_r2_r5 :
    leavesMod3Lens.view r2 = leavesMod3Lens.view r5 := by decide

/-- r2 vs r5: different parity. -/
theorem parity_distinguishes_r2_r5 :
    parityLens.view r2 ≠ parityLens.view r5 := by decide

/-- **leavesMod3Lens 는 parityLens 를 refine 하지 않음**. -/
theorem mod3_not_refines_parity :
    ¬ leavesMod3Lens.refines parityLens := by
  intro h
  exact parity_distinguishes_r2_r5 (h r2 r5 mod3_equates_r2_r5)

end E213.Research.Mod2Mod3Incomparable
