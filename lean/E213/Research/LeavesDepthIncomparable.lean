import E213.Hypervisor.Lens

/-!
# Research.LeavesDepthIncomparable

**주장**: `Lens.leaves` 와 `Lens.depth` 는 refines preorder
에서 **incomparable** — 서로 refine 하지 않음.

둘 다 Nat-valued 이지만 서로 다른 정보를 추출 (leaf count vs
tree height).  직관적으로 naturally 는 상관 있을 것 같지만,
Raw 의 쌍(n, depth) 분포가 충분히 풍부하여 둘 다 독립.

### Witnesses

- `leaves_not_refines_depth`: rDeep / rBalanced 가 같은 leaves
  (5), 다른 depth (4 vs 3).
- `depth_not_refines_leaves`: rShallowNarrow / rShallowWide 가
  같은 depth (3), 다른 leaves (4 vs 6).
-/

namespace E213.Research.LeavesDepthIncomparable

open E213.Firmware E213.Hypervisor

/-- Deep witness: `a / (b / (a / (a/b)))`, leaves=5, depth=4. -/
def rDeep : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.b
      (Raw.slash Raw.a
        (Raw.slash Raw.a Raw.b (by decide)) (by decide))
      (by decide))
    (by decide)

/-- Balanced witness: `(a/b) / (a / (a/b))`, leaves=5, depth=3. -/
def rBalanced : Raw :=
  Raw.slash
    (Raw.slash Raw.a Raw.b (by decide))
    (Raw.slash Raw.a
      (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

/-- Lens.leaves 은 rDeep, rBalanced 를 equate (둘 다 5). -/
theorem leaves_equates :
    Lens.leaves.view rDeep = Lens.leaves.view rBalanced := by decide

/-- Lens.depth 는 둘을 distinguish (4 vs 3). -/
theorem depth_distinguishes :
    Lens.depth.view rDeep ≠ Lens.depth.view rBalanced := by decide

/-- **leaves 는 depth 를 refine 하지 않음**. -/
theorem leaves_not_refines_depth : ¬ Lens.leaves.refines Lens.depth := by
  intro h
  exact depth_distinguishes (h rDeep rBalanced leaves_equates)

end E213.Research.LeavesDepthIncomparable

namespace E213.Research.LeavesDepthIncomparable

open E213.Firmware E213.Hypervisor

/-- Shallow narrow witness: `a / ((a/b) / b)`, leaves=4, depth=3. -/
def rShallowNarrow : Raw :=
  Raw.slash Raw.a
    (Raw.slash (Raw.slash Raw.a Raw.b (by decide)) Raw.b (by decide))
    (by decide)

/-- Shallow wide witness: `(a/(a/b)) / (b/(a/b))`, leaves=6, depth=3. -/
def rShallowWide : Raw :=
  Raw.slash
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

theorem depth_equates :
    Lens.depth.view rShallowNarrow = Lens.depth.view rShallowWide := by decide

theorem leaves_distinguishes :
    Lens.leaves.view rShallowNarrow ≠ Lens.leaves.view rShallowWide := by decide

/-- **depth 는 leaves 를 refine 하지 않음**. -/
theorem depth_not_refines_leaves : ¬ Lens.depth.refines Lens.leaves := by
  intro h
  exact leaves_distinguishes (h rShallowNarrow rShallowWide depth_equates)

end E213.Research.LeavesDepthIncomparable
