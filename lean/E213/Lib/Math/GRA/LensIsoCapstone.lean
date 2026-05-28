import E213.Lens.Unified
import E213.Lib.Math.GRA.LensBridge
import E213.Lib.Math.GRA.Universality23
import E213.Lib.Math.GRA.CarrierRealization

/-!
# GRA × Lens.Unified — Phase 22 capstone

The deepest 213-native statement of GRA's content: **the (2, 3)
grade arithmetic is the `LensIso`-equivalence class containing
the canonical grade-Lens**.

Components:
  · `gradeLens : Lens Nat` — the 213-native Lens whose view is
    `Raw.fold 2 3 (· + ·)` (= `canonicalGradeMap` of Phase 16).
  · `gradeLens_view_eq_canonical` — the Lens view IS the GRA
    canonical grade map by definitional unfolding.
  · `profile_view_eq_canonical` — Phase 18's universal property
    transported into Lens vocabulary: any Lens whose view
    satisfies the (2, 3)-profile (`view Raw.a = 2`, `view Raw.b
    = 3`, `view (slash x y h) = view x + view y`) has the same
    view function as `gradeLens` — hence the same kernel on
    Raw.
  · `profile_lens_LensIso_gradeLens` — by
    `Lens.Unified.lensIso_iff_kernel_eq`, every (2, 3)-profile
    Lens on Nat is `LensIso` to `gradeLens`.
  · Capstones for the five enrichments and for the canonical
    realization (Phase 17): each is an explicit `LensIso`.

This is the deepest connection of GRA back to Raw: the 213
substrate produces a **unique LensIso class** — the (2, 3)-arithmetic
class — and every "Reading" Phase 12 enumerated is a Lens-equal
representative.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.LensIsoCapstone

open E213.Theory E213.Lens
open E213.Lens.Unified (LensIso lensIso_iff_kernel_eq)
open E213.Lib.Math.GRA.LensBridge
open E213.Lib.Math.GRA.Universality23
  (canonicalGradeMap_universal canonical_arithmetic_forced)
open E213.Lib.Math.GRA.CarrierRealization

/-! ### §1 — The canonical grade-Lens on Nat

`gradeLens : Lens Nat` with `(base_a, base_b, combine) = (2, 3,
(· + ·))`.  By construction `gradeLens.view = Raw.fold 2 3 (· + ·) =
canonicalGradeMap` (definitionally).
-/

/-- The canonical (2, 3)-grade Lens.  `base_a = 2`, `base_b = 3`,
    `combine = Nat.add`. -/
def gradeLens : Lens Nat := ⟨2, 3, (· + ·)⟩

/-- The Lens view of `gradeLens` is *definitionally* the GRA
    canonical grade map. -/
theorem gradeLens_view_eq_canonical (r : Raw) :
    gradeLens.view r = canonicalGradeMap r := rfl

/-- Atomic values of `gradeLens`: `Raw.a ↦ 2`, `Raw.b ↦ 3`. -/
theorem gradeLens_view_a : gradeLens.view Raw.a = 2 := rfl
theorem gradeLens_view_b : gradeLens.view Raw.b = 3 := rfl

/-- Slash additivity at the Lens level: derived from
    `canonicalGradeMap_slash`. -/
theorem gradeLens_view_slash (x y : Raw) (h : x ≠ y) :
    gradeLens.view (Raw.slash x y h) =
    gradeLens.view x + gradeLens.view y :=
  canonicalGradeMap_slash x y h

/-! ### §2 — Phase 18 in Lens vocabulary

Any `Lens Nat` whose view satisfies the (2, 3)-profile has the
same view as `gradeLens` (pointwise), by Phase 18's universal
property.
-/

/-- Phase 18's universal property re-expressed at the Lens level:
    any Lens whose view matches the (2, 3)-profile coincides
    with `gradeLens` pointwise on Raw. -/
theorem profile_view_eq_canonical (L : Lens Nat)
    (ha : L.view Raw.a = 2)
    (hb : L.view Raw.b = 3)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              L.view (Raw.slash x y h) = L.view x + L.view y)
    (r : Raw) :
    L.view r = gradeLens.view r := by
  show L.view r = canonicalGradeMap r
  exact canonicalGradeMap_universal L.view ha hb hslash r

/-- The view-equality forces equiv-equivalence on Raw. -/
theorem profile_lens_equiv_eq_gradeLens (L : Lens Nat)
    (ha : L.view Raw.a = 2)
    (hb : L.view Raw.b = 3)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              L.view (Raw.slash x y h) = L.view x + L.view y)
    (x y : Raw) :
    L.equiv x y ↔ gradeLens.equiv x y := by
  show (L.view x = L.view y) ↔ (gradeLens.view x = gradeLens.view y)
  rw [profile_view_eq_canonical L ha hb hslash x,
      profile_view_eq_canonical L ha hb hslash y]

/-! ### §3 — The headline `LensIso` capstone

Every (2, 3)-profile Lens on Nat is `LensIso` to `gradeLens`.
This is the strongest 213-native statement of GRA's content:
the (2, 3)-arithmetic is an equivalence class under `LensIso`,
and `gradeLens` is the canonical representative.
-/

/-- **Phase 22 capstone**: every (2, 3)-profile Lens on Nat is
    `LensIso` to the canonical `gradeLens`.  The (2, 3)-grade
    arithmetic occupies a single equivalence class under
    `Lens.Unified.LensIso`. -/
theorem profile_lens_LensIso_gradeLens (L : Lens Nat)
    (ha : L.view Raw.a = 2)
    (hb : L.view Raw.b = 3)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              L.view (Raw.slash x y h) = L.view x + L.view y) :
    LensIso L gradeLens :=
  (lensIso_iff_kernel_eq L gradeLens).mpr
    (profile_lens_equiv_eq_gradeLens L ha hb hslash)

/-! ### §4 — Five Reading Lenses

Each enrichment of Phase 12 (Walk / Cochain / Truncation /
Operad / Resolution) has a grade map `Raw → Carrier → Nat` that
equals `canonicalGradeMap` by definition (Phase 16).  Packaging
this as a Lens and applying Phase 22 yields explicit `LensIso`
to `gradeLens`.

We construct the canonical Lens version of each enrichment grade
map by re-using `gradeLens` directly (the enrichment grade maps
ARE `canonicalGradeMap` by Phase 16's choices), so each
"Reading Lens" is *definitionally* `gradeLens`.  The point of
this section is to show that ANY Lens with the same atomic
profile, regardless of internal construction, is `LensIso` —
the equivalence class is uniquely determined by the (2, 3)
atomic data.
-/

/-- The "walk" Lens: a copy of `gradeLens` tagged for the R₄
    Reading.  By Phase 16 `walkGradeMap = canonicalGradeMap`,
    so the Lens views are equal. -/
def walkLens : Lens Nat := gradeLens
def cochainLens : Lens Nat := gradeLens
def truncationLens : Lens Nat := gradeLens
def operadLens : Lens Nat := gradeLens
def resolutionLens : Lens Nat := gradeLens

/-- Every Reading Lens is `LensIso` to `gradeLens`. -/
theorem walkLens_LensIso : LensIso walkLens gradeLens :=
  ⟨fun _ _ => id, fun _ _ => id⟩

theorem cochainLens_LensIso : LensIso cochainLens gradeLens :=
  ⟨fun _ _ => id, fun _ _ => id⟩

theorem truncationLens_LensIso : LensIso truncationLens gradeLens :=
  ⟨fun _ _ => id, fun _ _ => id⟩

theorem operadLens_LensIso : LensIso operadLens gradeLens :=
  ⟨fun _ _ => id, fun _ _ => id⟩

theorem resolutionLens_LensIso : LensIso resolutionLens gradeLens :=
  ⟨fun _ _ => id, fun _ _ => id⟩

/-! ### §5 — All-five pairwise `LensIso`

By `LensIso`'s transitivity (Phase 7 GRAIso-style closure) or
directly by `rfl` (since all five are `gradeLens`), every pair
of Reading Lenses is `LensIso`.
-/

/-- All five Reading Lenses sit in the same `LensIso` class. -/
theorem all_reading_lenses_LensIso :
    LensIso walkLens cochainLens ∧
    LensIso walkLens truncationLens ∧
    LensIso walkLens operadLens ∧
    LensIso walkLens resolutionLens ∧
    LensIso truncationLens operadLens :=
  ⟨⟨fun _ _ => id, fun _ _ => id⟩,
   ⟨fun _ _ => id, fun _ _ => id⟩,
   ⟨fun _ _ => id, fun _ _ => id⟩,
   ⟨fun _ _ => id, fun _ _ => id⟩,
   ⟨fun _ _ => id, fun _ _ => id⟩⟩

/-! ### §6 — Carrier-level forcing back into Raw via realizations

Each Phase 17 realization (e.g., `walkRealize : Raw → EdgeWalk`)
projects back to `canonicalGradeMap` at the Nat level.  Composed
with the grade projection, the resulting Raw → Nat is exactly
`gradeLens.view`.  This is the carrier-level confirmation of
the LensIso equivalence — at the *enriched* carrier, the same
arithmetic is being read.
-/

/-- Walk realization's grade-projection equals `gradeLens.view`. -/
theorem walkRealize_grade_eq_lens (r : Raw) :
    (walkRealize r).length = gradeLens.view r := rfl

theorem cochainRealize_grade_eq_lens (r : Raw) :
    (cochainRealize r).degree = gradeLens.view r := rfl

theorem truncationRealize_grade_eq_lens (r : Raw) :
    (truncationRealize r).level = gradeLens.view r := rfl

theorem operadRealize_grade_eq_lens (r : Raw) :
    (operadRealize r).level = gradeLens.view r := rfl

theorem resolutionRealize_grade_eq_lens (r : Raw) :
    (resolutionRealize r).exponent = gradeLens.view r := rfl

/-! ### §7 — Master capstone

The 213 substrate Raw, viewed through the (2, 3)-Lens, produces
a single equivalence class under `LensIso`.  `gradeLens` is the
canonical member; the five Reading Lenses are definitionally
equal members; the five enriched realizations project to the
same view.  The Lens-content of "(2, 3)-arithmetic forced by
atomic distinguishing" is captured *exactly* by this LensIso
class.
-/

/-- The (2, 3)-LensIso class is non-empty and contains the
    canonical `gradeLens`. -/
theorem gradeLens_in_LensIso_class : LensIso gradeLens gradeLens :=
  ⟨fun _ _ => id, fun _ _ => id⟩

/-- **Phase 22 master capstone**: the GRA (2, 3) arithmetic is
    the LensIso-equivalence class of `gradeLens`.  Any
    profile-respecting Lens on Nat is in the class; the five
    Reading Lenses are explicit members; the five enriched
    realizations project to `gradeLens.view` exactly. -/
def gra_lens_iso_class_capstone : Prop :=
  -- Every profile Lens is LensIso to gradeLens
  (∀ L : Lens Nat,
   L.view Raw.a = 2 → L.view Raw.b = 3 →
   (∀ x y h, L.view (Raw.slash x y h) = L.view x + L.view y) →
   LensIso L gradeLens) ∧
  -- The five Reading Lenses are all LensIso to gradeLens
  (LensIso walkLens gradeLens ∧
   LensIso cochainLens gradeLens ∧
   LensIso truncationLens gradeLens ∧
   LensIso operadLens gradeLens ∧
   LensIso resolutionLens gradeLens)

/-- The capstone is inhabited. -/
theorem gra_lens_iso_class_capstone_holds : gra_lens_iso_class_capstone :=
  ⟨fun L ha hb hslash => profile_lens_LensIso_gradeLens L ha hb hslash,
   walkLens_LensIso, cochainLens_LensIso, truncationLens_LensIso,
   operadLens_LensIso, resolutionLens_LensIso⟩

end E213.Lib.Math.GRA.LensIsoCapstone
