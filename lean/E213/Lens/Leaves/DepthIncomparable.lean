import E213.Lens.LensCore

/-!
# DepthIncomparable
**Claim**: `Lens.leaves` and `Lens.depth` are **incomparable** in the
refines preorder — neither refines the other.

Both are Nat-valued but extract different information (leaf count vs
tree height).  Intuitively they seem related, but the distribution of
pairs (n, depth) in Raw is rich enough that both are independent.

### Witnesses

- `leaves_not_refines_depth`: rDeep / rBalanced have equal leaves
  (5) but different depth (4 vs 3).
- `depth_not_refines_leaves`: rShallowNarrow / rShallowWide have
  equal depth (3) but different leaves (4 vs 6).
-/

namespace E213.Lens.Leaves.DepthIncomparable

open E213.Theory E213.Lens

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

/-- Lens.leaves equates rDeep and rBalanced (both 5). -/
theorem leaves_equates :
    Lens.leaves.view rDeep = Lens.leaves.view rBalanced := by decide

/-- Lens.depth distinguishes them (4 vs 3). -/
theorem depth_distinguishes :
    Lens.depth.view rDeep ≠ Lens.depth.view rBalanced := by decide

/-- **leaves does not refine depth**. -/
theorem leaves_not_refines_depth : ¬ Lens.leaves.refines Lens.depth := by
  intro h
  exact depth_distinguishes (h rDeep rBalanced leaves_equates)

end E213.Lens.Leaves.DepthIncomparable

namespace E213.Lens.Leaves.DepthIncomparable

open E213.Theory E213.Lens

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

/-- **depth does not refine leaves**. -/
theorem depth_not_refines_leaves : ¬ Lens.depth.refines Lens.leaves := by
  intro h
  exact leaves_distinguishes (h rShallowNarrow rShallowWide depth_equates)

end E213.Lens.Leaves.DepthIncomparable
