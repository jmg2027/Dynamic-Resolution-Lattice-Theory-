import E213.Lib.Math.GRA.LensBridge
import E213.Lib.Math.GRA.CarrierRealization

/-!
# GRA Universality of `canonicalGradeMap` — Phase 18

The next open frontier from Phase 17's essay revision is the
2-categorical statement "`GRACat`-as-a-`Cat` is a Reading of GRA".
A full 2-categorical formulation requires universe machinery
that 213's parameterless arithmetic deliberately avoids.  We
take the route that *does* fit the strict-∅-axiom discipline:
the **universal property of `canonicalGradeMap`**.

**Statement** (informal).  Any function `f : Raw → Nat` that
sends `Raw.a ↦ 2`, `Raw.b ↦ 3`, and respects `Raw.slash` by
addition (`f (slash x y h) = f x + f y`) equals
`canonicalGradeMap` pointwise.

**Why this closes the Cat-as-Reading concept rigorously**.  Any
"category of (2, 3)-arithmetic structures" carries a grade map
from Raw (via the universal morphism into the structure's
carrier).  The universal property forces that grade map to be
`canonicalGradeMap`.  Hence Cat / HoTT / Cohomology / Walk /
Resolution / Operad — any structure with two distinguished
elements at grades 2 and 3 plus grade-additive combination —
*is* the same arithmetic at the Raw-projection level.

The 2-categorical step ("Cat-as-Cat is a Reading of itself")
would need a `HasDistinguishing` on `Cat` (or `GRACat`)
objects — strictly impossible without universe lifting.  The
universal property is the parameterless 1-categorical proxy.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.Universality23

open E213.Theory
open E213.Lib.Math.GRA.LensBridge
open E213.Lib.Math.GRA.CarrierRealization

/-! ### §1 — Universal property of `canonicalGradeMap`

Any `f : Raw → Nat` with the (2, 3)-atom + slash-additive
profile equals `canonicalGradeMap` pointwise.
-/

/-- **Universal property of canonicalGradeMap**: any function
    `f : Raw → Nat` matching `canonicalGradeMap` on atoms and
    slash agrees with it pointwise.  Proof is Raw induction. -/
theorem canonicalGradeMap_universal (f : Raw → Nat)
    (ha : f Raw.a = 2) (hb : f Raw.b = 3)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = f x + f y)
    (r : Raw) :
    f r = canonicalGradeMap r := by
  induction r using Raw.rec with
  | a => rw [ha, canonicalGradeMap_a]
  | b => rw [hb, canonicalGradeMap_b]
  | slash x y h ihx ihy =>
    rw [hslash x y h, canonicalGradeMap_slash x y h, ihx, ihy]

/-! ### §2 — Specialised universal property: the enrichment grade map

The bipartite enrichment's grade map `bipartiteGradeMap`
satisfies the (2, 3)-profile, so by the universal property it
equals `canonicalGradeMap`.  This is already true `rfl` by
definition; the universal-property derivation makes the
*forced-by-arithmetic* nature explicit.
-/

theorem bipartiteGradeMap_forced (r : Raw) :
    bipartiteGradeMap r = canonicalGradeMap r :=
  canonicalGradeMap_universal bipartiteGradeMap
    bipartiteGradeMap_a bipartiteGradeMap_b bipartiteGradeMap_slash r

/-! ### §3 — Carrier-level forcing via the realization

`bipartiteRealize` of Phase 17 gives, for each Raw, an enriched
`BipartiteCarrier` element with `canonicalGradeMap` grade.
Combined with the universal property, this says: any enriched
(2, 3)-realization equals the canonical one at the grade level.
-/

theorem bipartiteRealize_grade_forced (r : Raw) :
    (bipartiteRealize r).n = canonicalGradeMap r := rfl

/-! ### §4 — The two-function uniqueness theorem

Two functions `f, g : Raw → Nat` that both match the (2, 3)-
profile must agree pointwise.  This is the contrapositive way
to state "the (2, 3)-arithmetic is unique."
-/

/-- Two (2, 3)-profile functions agree on every Raw. -/
theorem two_atoms_slash_agree (f g : Raw → Nat)
    (fa : f Raw.a = 2) (fb : f Raw.b = 3)
    (fslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = f x + f y)
    (ga : g Raw.a = 2) (gb : g Raw.b = 3)
    (gslash : ∀ (x y : Raw) (h : x ≠ y),
              g (Raw.slash x y h) = g x + g y)
    (r : Raw) :
    f r = g r := by
  rw [canonicalGradeMap_universal f fa fb fslash r,
      ← canonicalGradeMap_universal g ga gb gslash r]

/-! ### §5 — Categorical reading

The universal property is the parameterless analog of
"`canonicalGradeMap` is the unique morphism from `Raw` to `Nat`
in the category of (2, 3)-grade structures."  Any `Cat`-object
whose grade map satisfies the (2, 3)-profile receives a
canonical map *forced* to be `canonicalGradeMap`.  This is the
strongest 1-categorical statement of "Cat / HoTT / etc. are
Readings of GRA" available without universe lifting.
-/

/-- **Forcing capstone**: any Raw → Nat function with the
    canonical (2, 3)-profile equals `canonicalGradeMap`.  This
    is the formal statement that "the (2, 3) arithmetic is
    parameterlessly forced by atomic distinguishing." -/
theorem canonical_arithmetic_forced (f : Raw → Nat)
    (ha : f Raw.a = 2) (hb : f Raw.b = 3)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = f x + f y) :
    ∀ r : Raw, f r = canonicalGradeMap r :=
  fun r => canonicalGradeMap_universal f ha hb hslash r

end E213.Lib.Math.GRA.Universality23
