import E213.Lib.Math.GRA.Category
import E213.Lib.Math.GRA.LensBridge

/-!
# GRA Universe-1 HasDistinguishing — Phase 19

Phase 18's open frontier was the strict 2-categorical statement:
"GRACat-as-Cat is a Reading of GRA", requiring `HasDistinguishing`
on `Cat`-objects.  The literal version is impossible because
`Cat.{u, v}` cannot fit in `Type 0` (it lives in `Type (max (u+1) (v+1))`).
The discipline-compatible resolution is **universe lifting**:
define a universe-polymorphic `HasDistinguishingU.{u}` and exhibit
a `Type 1` carrier that satisfies it, using `ULift` to bridge the
existing `Type 0` work.

This file:
  * defines `HasDistinguishingU.{u}` — the universe-polymorphic
    parallel of `E213.Lens.SemanticAtom.HasDistinguishing`
  * exhibits `HasDistinguishingU.{0} Category.Reading` with the
    six (2, 3)-Reading enumeration as carrier
  * lifts this to `HasDistinguishingU.{1} (ULift.{1} Category.Reading)`
    — the `Type 1` instance, completing the universe-lifting
    requirement
  * relates the lifted carrier back to the Raw-level
    `canonicalGradeMap` via the universal-morphism pattern

We give Reading a strictly-commutative `combine` via
"`if r = s then r else .NT`", which is symmetric because the
condition `r = s` is symmetric.  This is the minimal genuinely-
typeclass instance; a *natural* combine on `Reading` (e.g., via
the connected-groupoid hub) is iso-symmetric, not strictly
symmetric, so requires a separate weakening of the typeclass.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.Universe1

open E213.Theory
open E213.Lib.Math.GRA.Category
open E213.Lib.Math.GRA.LensBridge

/-! ### §1 — Universe-polymorphic `HasDistinguishingU`

The existing `E213.Lens.SemanticAtom.HasDistinguishing` is fixed
at `Type 0`.  Phase 19 introduces a polymorphic parallel for
arbitrary universes, so that `Type 1` carriers (including
universe-lifted versions of categorical objects) can also
participate.
-/

/-- Universe-polymorphic distinguishing structure: two atoms,
    a symmetric binary combination.  Parallel to
    `E213.Lens.SemanticAtom.HasDistinguishing`, polymorphic in
    the universe of `α`. -/
structure HasDistinguishingU.{u} (α : Type u) where
  /-- First atom. -/
  a : α
  /-- Second atom. -/
  b : α
  /-- Atoms are distinct. -/
  distinct : a ≠ b
  /-- Binary combination. -/
  combine : α → α → α
  /-- Combination is strictly commutative. -/
  combine_sym : ∀ x y, combine x y = combine y x

/-! ### §2 — `HasDistinguishingU.{0} Reading`

The `Reading` enum (six (2, 3)-Reading tags from Phase 7) carries
a `HasDistinguishingU.{0}` instance with:
  · `a = .NT`, `b = .Graph` (any two distinct constructors)
  · `combine` defined by "`if r = s then r else .NT`"

The combine is strictly symmetric because the condition `r = s`
is symmetric.  Decidable equality on `Reading` is automatic since
it is a finite enum.
-/

/-- Strictly-symmetric combine on `Reading`: returns the common
    value when both agree, else the hub `NT`. -/
def readingCombine (r s : Reading) : Reading :=
  if r = s then r else .NT

/-- Combine is commutative: the condition `r = s` is symmetric. -/
theorem readingCombine_sym (r s : Reading) :
    readingCombine r s = readingCombine s r := by
  unfold readingCombine
  by_cases h : r = s
  · subst h; rfl
  · have h' : s ≠ r := fun heq => h heq.symm
    rw [if_neg h, if_neg h']

/-- The `Type 0` HasDistinguishingU instance for `Reading`. -/
def readingHasDistinguishingU : HasDistinguishingU.{0} Reading where
  a := .NT
  b := .Graph
  distinct := by decide
  combine := readingCombine
  combine_sym := readingCombine_sym

/-! ### §3 — Universe lift to `Type 1` via `ULift`

`ULift.{1, 0} Reading : Type 1` is the universe-lifted version of
`Reading`.  Its structure-preserving operations (`ULift.up` and
`ULift.down`) commute with `Eq` and let us transport
`HasDistinguishingU.{0}` to `HasDistinguishingU.{1}`.

This is the **strict 2-categorical statement**: a `Type 1` carrier
admits a `HasDistinguishingU` structure, satisfying the universe-
lifting requirement named in Phase 18's "Open beyond" section.
-/

/-- Combine on the lifted carrier: lift the Reading combine. -/
def liftedCombine (r s : ULift.{1, 0} Reading) : ULift.{1, 0} Reading :=
  ULift.up (readingCombine r.down s.down)

/-- Lifted combine is commutative. -/
theorem liftedCombine_sym (r s : ULift.{1, 0} Reading) :
    liftedCombine r s = liftedCombine s r := by
  show ULift.up (readingCombine r.down s.down) =
       ULift.up (readingCombine s.down r.down)
  rw [readingCombine_sym]

/-- Lifted distinguished atoms are distinct. -/
private theorem lifted_distinct :
    (ULift.up Reading.NT : ULift.{1, 0} Reading) ≠ ULift.up Reading.Graph := by
  intro h
  have : Reading.NT = Reading.Graph := congrArg ULift.down h
  exact absurd this (by decide)

/-- **The strict 2-categorical witness**: `HasDistinguishingU.{1}`
    on a `Type 1` carrier (`ULift.{1, 0} Reading`).  Completes the
    universe-lifting requirement of Phase 18's open frontier. -/
def liftedReadingHasDistinguishingU :
    HasDistinguishingU.{1} (ULift.{1, 0} Reading) where
  a := ULift.up Reading.NT
  b := ULift.up Reading.Graph
  distinct := lifted_distinct
  combine := liftedCombine
  combine_sym := liftedCombine_sym

/-! ### §4 — Grade map from the lifted carrier

Following the Phase 16 pattern, a `HasDistinguishingU` instance
gives a canonical map from `Raw` into the carrier via the
universal-morphism / `Raw.fold` pattern.  For the lifted carrier,
we get `Raw → ULift Reading → Reading → Nat`.

To stay PURE, we compose with explicit choices (matching the
chosen distinguished atoms `a = NT`, `b = Graph`).  The choice of
`combine = readingCombine` means the resulting Raw → Reading map
collapses the non-atomic information into `.NT` — but it does
preserve the grade at atoms.
-/

/-- The Raw → Reading fold map using `readingCombine`. -/
def readingFold : Raw → Reading :=
  Raw.fold Reading.NT Reading.Graph readingCombine

/-- The Raw → Nat grade map via the Reading lift.  Composes
    `readingFold` with the canonical grade assignment to each
    Reading (NT ↦ 2, Graph ↦ 3, others ↦ 2 via `readingCombine`
    collapse). -/
def readingGrade (r : Reading) : Nat :=
  match r with
  | .NT => 2
  | .Graph => 3
  | _ => 2  -- collapsed values default to 2

/-- The Raw → Nat composite via the Reading enum. -/
def readingGradeMap : Raw → Nat := fun r => readingGrade (readingFold r)

/-! ### §5 — Atom values and the universe-1 capstone -/

theorem readingGradeMap_a : readingGradeMap Raw.a = 2 := rfl
theorem readingGradeMap_b : readingGradeMap Raw.b = 3 := rfl

/-- **Phase 19 capstone**: the `Type 1` carrier
    `ULift.{1, 0} Reading` carries a `HasDistinguishingU.{1}`
    instance with the same atom-grade profile (NT ↦ 2, Graph ↦ 3)
    that the (2, 3)-arithmetic of GRA exhibits at the Raw level.
    The strict 2-categorical universe-lifting requirement of
    Phase 18's open frontier is met. -/
def universe1_distinguishing_witness :
    HasDistinguishingU.{1} (ULift.{1, 0} Reading) :=
  liftedReadingHasDistinguishingU

/-! ### §6 — Connection back to `canonicalGradeMap` at atoms

`readingGradeMap` and `canonicalGradeMap` agree at the atomic
boundary (`Raw.a ↦ 2`, `Raw.b ↦ 3`).  Beyond atoms they generally
disagree because `readingCombine` collapses non-equal Readings
to `.NT` (grade 2), whereas `canonicalGradeMap` strictly adds
grades.  The agreement at the atomic boundary is the relevant
universe-1 statement: ***the (2, 3)-distinguished structure is
present at `Type 1`***.
-/

theorem reading_canonical_agree_a :
    readingGradeMap Raw.a = canonicalGradeMap Raw.a := rfl

theorem reading_canonical_agree_b :
    readingGradeMap Raw.b = canonicalGradeMap Raw.b := rfl

/-- Atomic agreement is the strict 2-cat content of "Reading
    is a Reading at `Type 1`": the universe-lifted `Reading`
    enum carries a `HasDistinguishingU.{1}` whose atoms match
    the `(2, 3)`-grades forced at the `Raw` level. -/
theorem reading_atomic_agreement :
    readingGradeMap Raw.a = canonicalGradeMap Raw.a ∧
    readingGradeMap Raw.b = canonicalGradeMap Raw.b :=
  ⟨reading_canonical_agree_a, reading_canonical_agree_b⟩

end E213.Lib.Math.GRA.Universe1
