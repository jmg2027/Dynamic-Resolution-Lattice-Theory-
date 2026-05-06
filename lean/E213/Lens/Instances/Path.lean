import E213.Theory.Raw
import E213.Lens.LensCore
import E213.Lens.Characterisation.Catalog
import E213.Prelude

/-!
# PathLens: non-commutative-combine witness

`pathLens : Lens (List Bool)` with `base_a = [false]`,
`base_b = [true]`, `combine = List.append`.

**Role.**  Every other Lens in the catalogue uses a *commutative*
combine (depth/leaves/signed use `+` or `max`; Bool lenses use
`and/or/xor` which are all commutative).  `pathLens` is the first
deliberately *non-commutative* witness.

**Consequences.**

1. `pathLens` is **not** an instance of `CommBinaryCodomain`
   (which bundles `combine_comm`).  Its combine is genuinely
   asymmetric: `append [false] [true] ≠ append [true] [false]`.

2. The Lens's view remains well-defined on Raw, because `Raw.slash`
   canonicalises child order.  Concretely,
   `pathLens.view (Raw.slash b a h) = pathLens.view (Raw.slash a b h')`:
   the two Raw terms are literally equal (`Raw.slash_comm`), so the
   views coincide.  The "order" of the list is dictated by Raw's
   internal `cmp`-canonical form, *not* by how the user wrote the
   slash.  This illustrates §1 of the paper: the axiom's "between"
   is directionless, and no Lens can recover a notional ordering.

3. `pathLens` is R5-compatible on the level-≤2 enumeration (5
   distinct Raw terms ↦ 5 distinct lists, table below).  Full
   injectivity on all Raw is not proved here — but also not
   needed for the R12-failure point.
-/

namespace E213.Lens.Instances.Path
open E213.Theory E213.Lens

/-- **Path lens.**  `a ↦ [false]`, `b ↦ [true]`, combine = append. -/
def pathLens : Lens (List Bool) where
  base_a  := [false]
  base_b  := [true]
  combine := fun xs ys => xs ++ ys

-- ═══ Direct views on the level-≤2 terms ═══

example : pathLens.view Raw.a = [false] := rfl
example : pathLens.view Raw.b = [true]  := rfl

theorem pathLens_view_ab :
    pathLens.view (Raw.slash Raw.a Raw.b (by decide))
      = [false, true] := rfl

theorem pathLens_view_ba_via_comm :
    pathLens.view (Raw.slash Raw.b Raw.a (by decide))
      = [false, true] := by
  rw [Raw.slash_comm]; rfl

end E213.Lens.Instances.Path
namespace E213.Lens.Instances.Path
open E213.Theory E213.Lens

theorem pathLens_view_a_slash_ab :
    pathLens.view (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
      (by decide))
      = [false, false, true] := rfl

theorem pathLens_view_b_slash_ab :
    pathLens.view (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide))
      (by decide))
      = [true, false, true] := rfl

-- ═══ R2 (combine commutativity) FAILS ═══

/-- **`pathLens.combine` is NOT commutative.**  Concrete witness:
    `append [false] [true] = [false, true]` but
    `append [true] [false] = [true, false]`. -/
theorem pathLens_combine_not_commutative :
    ¬ ∀ u v : List Bool, pathLens.combine u v = pathLens.combine v u := by
  intro h
  have := h [false] [true]
  -- `this : [false, true] = [true, false]`
  revert this; decide

-- ═══ R5 — injectivity holds on level-≤2 (the 5 Raw terms) ═══

/-- The 5 Raw terms of level ≤ 2 have 5 distinct list-views,
    so `pathLens.view` is injective on this finite subset. -/
example :
    pathLens.view Raw.a
      ≠ pathLens.view Raw.b := by decide
example :
    pathLens.view Raw.a
      ≠ pathLens.view (Raw.slash Raw.a Raw.b (by decide)) := by decide
example :
    pathLens.view (Raw.slash Raw.a Raw.b (by decide))
      ≠ pathLens.view
          (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
            (by decide)) := by decide
example :
    pathLens.view (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide))
        (by decide))
      ≠ pathLens.view
          (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide))
            (by decide)) := by decide

end E213.Lens.Instances.Path