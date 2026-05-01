import E213.Research.Lens.Identity

/-!
# Research.RawMatchingLens: all Raw-matching Lenses have identity view

**Theorem**: if `L : Lens Raw` satisfies the following, then `L.view = id`:

1. `L.base_a = Raw.a`
2. `L.base_b = Raw.b`
3. `L.combine x y = Raw.slash x y h` for all `x ≠ y`.

The diagonal (`L.combine x x`) is free — it has no effect on view.

## Significance

`idLens` is a specific choice (diagonal = Raw.a).  This theorem shows that
**whenever Raw-level data agrees, view must be identity**.  That is, the
formal identity of idLens is independent of the diagonal choice.

A stronger form of the universal property: off-diagonal structure determines
view.  This is a stronger expression of the Note 34-35 observation that
"diagonal is meaningful only when present in view."
-/

namespace E213.Research.Lens.RawMatching

open E213.Firmware E213.Hypervisor E213.Research.IdentityLens

/-- A Lens satisfying the Raw-matching conditions with a free diagonal has view = id. -/
theorem rawMatching_view_is_id (L : Lens Raw)
    (hba : L.base_a = Raw.a)
    (hbb : L.base_b = Raw.b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              L.combine x y = Raw.slash x y h)
    (hsym : ∀ u v : Raw, L.combine u v = L.combine v u) :
    ∀ r : Raw, L.view r = r := by
  intro r
  induction r using Raw.rec with
  | a =>
      show L.base_a = Raw.a
      exact hba
  | b =>
      show L.base_b = Raw.b
      exact hbb
  | slash x y h ihx ihy =>
      have hfs : L.view (Raw.slash x y h)
                   = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hsym x y h
      rw [hfs, ihx, ihy]
      -- Now need: L.combine x y = Raw.slash x y h
      exact hslash x y h

end E213.Research.Lens.RawMatching
