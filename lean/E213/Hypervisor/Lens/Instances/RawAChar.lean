import E213.Hypervisor.Lens
import E213.Hypervisor.Lens.Compose.Factoring
import E213.Hypervisor.Lens.Properties.Leaf

/-!
# Research.RawACharLens: characteristic function of Raw.a is a Lens

**Observation**: `fun r => decide (r = Raw.a)` is a fold-structured function
(and therefore realizable as a Lens).

Implemented with combine = const false.

## Reason (why only leaves work)

- Raw.a is a leaf.  "s = Raw.a" is determined only in the base branch.
  The slash branch is automatically false (slash ≠ leaf).
- For a specific slash r such as Raw.slash x y h, "s = r" is
  not fold-structured — whether s = r cannot be determined from
  view x, view y alone (requires direct inspection of subtree structure).

**Leaves are observable via Lens; specific slashes are not observable**.

## New kernel class

2-class partition: {Raw.a} vs {everything else}.  Distinct from the
existing catalog's leafLens ({leaves} vs {slashes}).
-/

namespace E213.Hypervisor.Lens.Instances.RawAChar

open E213.Firmware E213.Hypervisor

/-- Characteristic Lens of Raw.a. -/
def rawACharLens : Lens Bool where
  base_a := true
  base_b := false
  combine _ _ := false

theorem rawACharLens_view_eq :
    ∀ r : Raw, rawACharLens.view r = decide (r = Raw.a) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : rawACharLens.view (Raw.slash x y h)
                   = rawACharLens.combine
                       (rawACharLens.view x) (rawACharLens.view y) := by
        apply Raw.fold_slash
        intro _ _; rfl
      rw [hfs]
      show (false : Bool) = decide (Raw.slash x y h = Raw.a)
      have hne : Raw.slash x y h ≠ Raw.a := by
        intro heq
        have hv : (Raw.slash x y h).val = Raw.a.val :=
          congrArg Subtype.val heq
        have hra : Raw.a.val = (.a : E213.Firmware.Internal.Tree) := rfl
        rw [hra] at hv
        unfold Raw.slash at hv
        split at hv <;> rename_i hcmp
        · exact E213.Firmware.Internal.Tree.noConfusion hv
        · exact E213.Firmware.Internal.Tree.noConfusion hv
        · exact h (Subtype.ext
            ((E213.Firmware.Internal.Tree.cmp_eq_iff _ _).mp hcmp))
      rw [decide_eq_false hne]

end E213.Hypervisor.Lens.Instances.RawAChar

namespace E213.Hypervisor.Lens.Instances.RawAChar

open E213.Firmware E213.Hypervisor E213.Hypervisor.Lens.Properties.Leaf

/-- Raw.a vs Raw.b: leafLens equates them, rawACharLens distinguishes them. -/
theorem leafLens_equates_a_b :
    leafLens.view Raw.a = leafLens.view Raw.b := rfl

theorem rawACharLens_distinguishes_a_b :
    rawACharLens.view Raw.a ≠ rawACharLens.view Raw.b := by decide

theorem leafLens_not_refines_rawACharLens :
    ¬ leafLens.refines rawACharLens := by
  intro h
  exact rawACharLens_distinguishes_a_b
    (h Raw.a Raw.b leafLens_equates_a_b)

/-- rawACharLens does not refine leafLens.
    Witness: Raw.b (a leaf, not Raw.a) vs slash(a, b).
    Both satisfy "≠ Raw.a" but leafLens distinguishes them (leaf vs slash). -/
theorem rawACharLens_not_refines_leafLens :
    ¬ rawACharLens.refines leafLens := by
  intro h
  let sab := Raw.slash Raw.a Raw.b (by decide)
  have hrawa_eq : rawACharLens.view Raw.b = rawACharLens.view sab := by decide
  have : leafLens.view Raw.b = leafLens.view sab := h _ _ hrawa_eq
  exact absurd this (by decide)

end E213.Hypervisor.Lens.Instances.RawAChar
